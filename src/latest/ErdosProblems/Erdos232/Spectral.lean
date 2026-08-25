/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactCertificates.Block00
import ErdosProblems.Erdos232.CompactCertificates.Block01
import ErdosProblems.Erdos232.CompactCertificates.Block02
import ErdosProblems.Erdos232.CompactCertificates.Block03
import ErdosProblems.Erdos232.CompactCertificates.Block04
import ErdosProblems.Erdos232.CompactCertificates.Block05
import ErdosProblems.Erdos232.CompactCertificates.Block06
import ErdosProblems.Erdos232.CompactCertificates.Block07
import ErdosProblems.Erdos232.CompactCertificates.Block08
import ErdosProblems.Erdos232.CompactCertificates.Block09
import ErdosProblems.Erdos232.CompactCertificates.Block10
import ErdosProblems.Erdos232.CompactCertificates.Block11
import ErdosProblems.Erdos232.CompactCertificates.Block12
import ErdosProblems.Erdos232.CompactCertificates.Block13
import ErdosProblems.Erdos232.CompactCertificates.Block14
import ErdosProblems.Erdos232.CompactCertificates.Block15
import ErdosProblems.Erdos232.Tail

open LeanCert.Core

namespace Erdos232

/-- Apply a compact certificate after identifying its exact ordered rational interval. -/
private theorem compactCertificate_proves_between
    (C : CompactCertificate)
    (hcert : ∀ {t : ℝ}, t ∈ C.interval →
      1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t)
    (a b : ℚ) (hab : a ≤ b) (hinterval : C.interval = orderedInterval a b)
    (t : ℝ) (hlo : (a : ℝ) ≤ t) (hhi : t ≤ (b : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  apply hcert
  rw [hinterval]
  simp only [IntervalRat.mem_def, orderedInterval, min_eq_left hab, max_eq_right hab]
  exact ⟨hlo, hhi⟩

private theorem dual_spectral_compact_000 (t : ℝ)
    (hlo : ((0) : ℝ) ≤ t) (hhi : t ≤ ((1 / 64) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate000
    (fun ht => compactCertificate000_proves ht) ((0) : ℚ) ((1 / 64) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_001 (t : ℝ)
    (hlo : ((1 / 64) : ℝ) ≤ t) (hhi : t ≤ ((1 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate001
    (fun ht => compactCertificate001_proves ht) ((1 / 64) : ℚ) ((1 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_002 (t : ℝ)
    (hlo : ((1 / 32) : ℝ) ≤ t) (hhi : t ≤ ((1 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate002
    (fun ht => compactCertificate002_proves ht) ((1 / 32) : ℚ) ((1 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_003 (t : ℝ)
    (hlo : ((1 / 16) : ℝ) ≤ t) (hhi : t ≤ ((1 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate003
    (fun ht => compactCertificate003_proves ht) ((1 / 16) : ℚ) ((1 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_004 (t : ℝ)
    (hlo : ((1 / 8) : ℝ) ≤ t) (hhi : t ≤ ((1 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate004
    (fun ht => compactCertificate004_proves ht) ((1 / 8) : ℚ) ((1 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_005 (t : ℝ)
    (hlo : ((1 / 4) : ℝ) ≤ t) (hhi : t ≤ ((1 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate005
    (fun ht => compactCertificate005_proves ht) ((1 / 4) : ℚ) ((1 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_006 (t : ℝ)
    (hlo : ((1 / 2) : ℝ) ≤ t) (hhi : t ≤ ((1) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate006
    (fun ht => compactCertificate006_proves ht) ((1 / 2) : ℚ) ((1) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_007 (t : ℝ)
    (hlo : ((1) : ℝ) ≤ t) (hhi : t ≤ ((2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate007
    (fun ht => compactCertificate007_proves ht) ((1) : ℚ) ((2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_008 (t : ℝ)
    (hlo : ((2) : ℝ) ≤ t) (hhi : t ≤ ((3) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate008
    (fun ht => compactCertificate008_proves ht) ((2) : ℚ) ((3) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_009 (t : ℝ)
    (hlo : ((3) : ℝ) ≤ t) (hhi : t ≤ ((13 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate009
    (fun ht => compactCertificate009_proves ht) ((3) : ℚ) ((13 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_010 (t : ℝ)
    (hlo : ((13 / 4) : ℝ) ≤ t) (hhi : t ≤ ((7 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate010
    (fun ht => compactCertificate010_proves ht) ((13 / 4) : ℚ) ((7 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_011 (t : ℝ)
    (hlo : ((7 / 2) : ℝ) ≤ t) (hhi : t ≤ ((29 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate011
    (fun ht => compactCertificate011_proves ht) ((7 / 2) : ℚ) ((29 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_012 (t : ℝ)
    (hlo : ((29 / 8) : ℝ) ≤ t) (hhi : t ≤ ((59 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate012
    (fun ht => compactCertificate012_proves ht) ((29 / 8) : ℚ) ((59 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_013 (t : ℝ)
    (hlo : ((59 / 16) : ℝ) ≤ t) (hhi : t ≤ ((119 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate013
    (fun ht => compactCertificate013_proves ht) ((59 / 16) : ℚ) ((119 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_014 (t : ℝ)
    (hlo : ((119 / 32) : ℝ) ≤ t) (hhi : t ≤ ((15 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate014
    (fun ht => compactCertificate014_proves ht) ((119 / 32) : ℚ) ((15 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_015 (t : ℝ)
    (hlo : ((15 / 4) : ℝ) ≤ t) (hhi : t ≤ ((121 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate015
    (fun ht => compactCertificate015_proves ht) ((15 / 4) : ℚ) ((121 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_016 (t : ℝ)
    (hlo : ((121 / 32) : ℝ) ≤ t) (hhi : t ≤ ((61 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate016
    (fun ht => compactCertificate016_proves ht) ((121 / 32) : ℚ) ((61 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_017 (t : ℝ)
    (hlo : ((61 / 16) : ℝ) ≤ t) (hhi : t ≤ ((31 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate017
    (fun ht => compactCertificate017_proves ht) ((61 / 16) : ℚ) ((31 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_018 (t : ℝ)
    (hlo : ((31 / 8) : ℝ) ≤ t) (hhi : t ≤ ((4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate018
    (fun ht => compactCertificate018_proves ht) ((31 / 8) : ℚ) ((4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_019 (t : ℝ)
    (hlo : ((4) : ℝ) ≤ t) (hhi : t ≤ ((9 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate019
    (fun ht => compactCertificate019_proves ht) ((4) : ℚ) ((9 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_020 (t : ℝ)
    (hlo : ((9 / 2) : ℝ) ≤ t) (hhi : t ≤ ((5) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate020
    (fun ht => compactCertificate020_proves ht) ((9 / 2) : ℚ) ((5) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_021 (t : ℝ)
    (hlo : ((5) : ℝ) ≤ t) (hhi : t ≤ ((11 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate021
    (fun ht => compactCertificate021_proves ht) ((5) : ℚ) ((11 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_022 (t : ℝ)
    (hlo : ((11 / 2) : ℝ) ≤ t) (hhi : t ≤ ((6) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate022
    (fun ht => compactCertificate022_proves ht) ((11 / 2) : ℚ) ((6) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_023 (t : ℝ)
    (hlo : ((6) : ℝ) ≤ t) (hhi : t ≤ ((49 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate023
    (fun ht => compactCertificate023_proves ht) ((6) : ℚ) ((49 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_024 (t : ℝ)
    (hlo : ((49 / 8) : ℝ) ≤ t) (hhi : t ≤ ((99 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate024
    (fun ht => compactCertificate024_proves ht) ((49 / 8) : ℚ) ((99 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_025 (t : ℝ)
    (hlo : ((99 / 16) : ℝ) ≤ t) (hhi : t ≤ ((25 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate025
    (fun ht => compactCertificate025_proves ht) ((99 / 16) : ℚ) ((25 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_026 (t : ℝ)
    (hlo : ((25 / 4) : ℝ) ≤ t) (hhi : t ≤ ((201 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate026
    (fun ht => compactCertificate026_proves ht) ((25 / 4) : ℚ) ((201 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_027 (t : ℝ)
    (hlo : ((201 / 32) : ℝ) ≤ t) (hhi : t ≤ ((101 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate027
    (fun ht => compactCertificate027_proves ht) ((201 / 32) : ℚ) ((101 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_028 (t : ℝ)
    (hlo : ((101 / 16) : ℝ) ≤ t) (hhi : t ≤ ((203 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate028
    (fun ht => compactCertificate028_proves ht) ((101 / 16) : ℚ) ((203 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_029 (t : ℝ)
    (hlo : ((203 / 32) : ℝ) ≤ t) (hhi : t ≤ ((51 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate029
    (fun ht => compactCertificate029_proves ht) ((203 / 32) : ℚ) ((51 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_030 (t : ℝ)
    (hlo : ((51 / 8) : ℝ) ≤ t) (hhi : t ≤ ((103 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate030
    (fun ht => compactCertificate030_proves ht) ((51 / 8) : ℚ) ((103 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_031 (t : ℝ)
    (hlo : ((103 / 16) : ℝ) ≤ t) (hhi : t ≤ ((13 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate031
    (fun ht => compactCertificate031_proves ht) ((103 / 16) : ℚ) ((13 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_032 (t : ℝ)
    (hlo : ((13 / 2) : ℝ) ≤ t) (hhi : t ≤ ((27 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate032
    (fun ht => compactCertificate032_proves ht) ((13 / 2) : ℚ) ((27 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_033 (t : ℝ)
    (hlo : ((27 / 4) : ℝ) ≤ t) (hhi : t ≤ ((7) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate033
    (fun ht => compactCertificate033_proves ht) ((27 / 4) : ℚ) ((7) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_034 (t : ℝ)
    (hlo : ((7) : ℝ) ≤ t) (hhi : t ≤ ((8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate034
    (fun ht => compactCertificate034_proves ht) ((7) : ℚ) ((8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_035 (t : ℝ)
    (hlo : ((8) : ℝ) ≤ t) (hhi : t ≤ ((9) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate035
    (fun ht => compactCertificate035_proves ht) ((8) : ℚ) ((9) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_036 (t : ℝ)
    (hlo : ((9) : ℝ) ≤ t) (hhi : t ≤ ((19 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate036
    (fun ht => compactCertificate036_proves ht) ((9) : ℚ) ((19 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_037 (t : ℝ)
    (hlo : ((19 / 2) : ℝ) ≤ t) (hhi : t ≤ ((39 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate037
    (fun ht => compactCertificate037_proves ht) ((19 / 2) : ℚ) ((39 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_038 (t : ℝ)
    (hlo : ((39 / 4) : ℝ) ≤ t) (hhi : t ≤ ((10) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate038
    (fun ht => compactCertificate038_proves ht) ((39 / 4) : ℚ) ((10) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_039 (t : ℝ)
    (hlo : ((10) : ℝ) ≤ t) (hhi : t ≤ ((81 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate039
    (fun ht => compactCertificate039_proves ht) ((10) : ℚ) ((81 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_040 (t : ℝ)
    (hlo : ((81 / 8) : ℝ) ≤ t) (hhi : t ≤ ((163 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate040
    (fun ht => compactCertificate040_proves ht) ((81 / 8) : ℚ) ((163 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_041 (t : ℝ)
    (hlo : ((163 / 16) : ℝ) ≤ t) (hhi : t ≤ ((41 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate041
    (fun ht => compactCertificate041_proves ht) ((163 / 16) : ℚ) ((41 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_042 (t : ℝ)
    (hlo : ((41 / 4) : ℝ) ≤ t) (hhi : t ≤ ((329 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate042
    (fun ht => compactCertificate042_proves ht) ((41 / 4) : ℚ) ((329 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_043 (t : ℝ)
    (hlo : ((329 / 32) : ℝ) ≤ t) (hhi : t ≤ ((165 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate043
    (fun ht => compactCertificate043_proves ht) ((329 / 32) : ℚ) ((165 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_044 (t : ℝ)
    (hlo : ((165 / 16) : ℝ) ≤ t) (hhi : t ≤ ((331 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate044
    (fun ht => compactCertificate044_proves ht) ((165 / 16) : ℚ) ((331 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_045 (t : ℝ)
    (hlo : ((331 / 32) : ℝ) ≤ t) (hhi : t ≤ ((83 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate045
    (fun ht => compactCertificate045_proves ht) ((331 / 32) : ℚ) ((83 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_046 (t : ℝ)
    (hlo : ((83 / 8) : ℝ) ≤ t) (hhi : t ≤ ((21 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate046
    (fun ht => compactCertificate046_proves ht) ((83 / 8) : ℚ) ((21 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_047 (t : ℝ)
    (hlo : ((21 / 2) : ℝ) ≤ t) (hhi : t ≤ ((43 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate047
    (fun ht => compactCertificate047_proves ht) ((21 / 2) : ℚ) ((43 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_048 (t : ℝ)
    (hlo : ((43 / 4) : ℝ) ≤ t) (hhi : t ≤ ((11) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate048
    (fun ht => compactCertificate048_proves ht) ((43 / 4) : ℚ) ((11) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_049 (t : ℝ)
    (hlo : ((11) : ℝ) ≤ t) (hhi : t ≤ ((23 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate049
    (fun ht => compactCertificate049_proves ht) ((11) : ℚ) ((23 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_050 (t : ℝ)
    (hlo : ((23 / 2) : ℝ) ≤ t) (hhi : t ≤ ((12) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate050
    (fun ht => compactCertificate050_proves ht) ((23 / 2) : ℚ) ((12) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_051 (t : ℝ)
    (hlo : ((12) : ℝ) ≤ t) (hhi : t ≤ ((13) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate051
    (fun ht => compactCertificate051_proves ht) ((12) : ℚ) ((13) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_052 (t : ℝ)
    (hlo : ((13) : ℝ) ≤ t) (hhi : t ≤ ((14) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate052
    (fun ht => compactCertificate052_proves ht) ((13) : ℚ) ((14) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_053 (t : ℝ)
    (hlo : ((14) : ℝ) ≤ t) (hhi : t ≤ ((15) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate053
    (fun ht => compactCertificate053_proves ht) ((14) : ℚ) ((15) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_054 (t : ℝ)
    (hlo : ((15) : ℝ) ≤ t) (hhi : t ≤ ((31 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate054
    (fun ht => compactCertificate054_proves ht) ((15) : ℚ) ((31 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_055 (t : ℝ)
    (hlo : ((31 / 2) : ℝ) ≤ t) (hhi : t ≤ ((16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate055
    (fun ht => compactCertificate055_proves ht) ((31 / 2) : ℚ) ((16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_056 (t : ℝ)
    (hlo : ((16) : ℝ) ≤ t) (hhi : t ≤ ((33 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate056
    (fun ht => compactCertificate056_proves ht) ((16) : ℚ) ((33 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_057 (t : ℝ)
    (hlo : ((33 / 2) : ℝ) ≤ t) (hhi : t ≤ ((67 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate057
    (fun ht => compactCertificate057_proves ht) ((33 / 2) : ℚ) ((67 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_058 (t : ℝ)
    (hlo : ((67 / 4) : ℝ) ≤ t) (hhi : t ≤ ((269 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate058
    (fun ht => compactCertificate058_proves ht) ((67 / 4) : ℚ) ((269 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_059 (t : ℝ)
    (hlo : ((269 / 16) : ℝ) ≤ t) (hhi : t ≤ ((539 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate059
    (fun ht => compactCertificate059_proves ht) ((269 / 16) : ℚ) ((539 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_060 (t : ℝ)
    (hlo : ((539 / 32) : ℝ) ≤ t) (hhi : t ≤ ((135 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate060
    (fun ht => compactCertificate060_proves ht) ((539 / 32) : ℚ) ((135 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_061 (t : ℝ)
    (hlo : ((135 / 8) : ℝ) ≤ t) (hhi : t ≤ ((541 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate061
    (fun ht => compactCertificate061_proves ht) ((135 / 8) : ℚ) ((541 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_062 (t : ℝ)
    (hlo : ((541 / 32) : ℝ) ≤ t) (hhi : t ≤ ((271 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate062
    (fun ht => compactCertificate062_proves ht) ((541 / 32) : ℚ) ((271 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_063 (t : ℝ)
    (hlo : ((271 / 16) : ℝ) ≤ t) (hhi : t ≤ ((17) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate063
    (fun ht => compactCertificate063_proves ht) ((271 / 16) : ℚ) ((17) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_064 (t : ℝ)
    (hlo : ((17) : ℝ) ≤ t) (hhi : t ≤ ((137 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate064
    (fun ht => compactCertificate064_proves ht) ((17) : ℚ) ((137 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_065 (t : ℝ)
    (hlo : ((137 / 8) : ℝ) ≤ t) (hhi : t ≤ ((69 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate065
    (fun ht => compactCertificate065_proves ht) ((137 / 8) : ℚ) ((69 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_066 (t : ℝ)
    (hlo : ((69 / 4) : ℝ) ≤ t) (hhi : t ≤ ((35 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate066
    (fun ht => compactCertificate066_proves ht) ((69 / 4) : ℚ) ((35 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_067 (t : ℝ)
    (hlo : ((35 / 2) : ℝ) ≤ t) (hhi : t ≤ ((18) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate067
    (fun ht => compactCertificate067_proves ht) ((35 / 2) : ℚ) ((18) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_068 (t : ℝ)
    (hlo : ((18) : ℝ) ≤ t) (hhi : t ≤ ((19) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate068
    (fun ht => compactCertificate068_proves ht) ((18) : ℚ) ((19) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_069 (t : ℝ)
    (hlo : ((19) : ℝ) ≤ t) (hhi : t ≤ ((20) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate069
    (fun ht => compactCertificate069_proves ht) ((19) : ℚ) ((20) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_070 (t : ℝ)
    (hlo : ((20) : ℝ) ≤ t) (hhi : t ≤ ((21) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate070
    (fun ht => compactCertificate070_proves ht) ((20) : ℚ) ((21) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_071 (t : ℝ)
    (hlo : ((21) : ℝ) ≤ t) (hhi : t ≤ ((22) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate071
    (fun ht => compactCertificate071_proves ht) ((21) : ℚ) ((22) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_072 (t : ℝ)
    (hlo : ((22) : ℝ) ≤ t) (hhi : t ≤ ((45 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate072
    (fun ht => compactCertificate072_proves ht) ((22) : ℚ) ((45 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_073 (t : ℝ)
    (hlo : ((45 / 2) : ℝ) ≤ t) (hhi : t ≤ ((23) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate073
    (fun ht => compactCertificate073_proves ht) ((45 / 2) : ℚ) ((23) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_074 (t : ℝ)
    (hlo : ((23) : ℝ) ≤ t) (hhi : t ≤ ((185 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate074
    (fun ht => compactCertificate074_proves ht) ((23) : ℚ) ((185 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_075 (t : ℝ)
    (hlo : ((185 / 8) : ℝ) ≤ t) (hhi : t ≤ ((93 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate075
    (fun ht => compactCertificate075_proves ht) ((185 / 8) : ℚ) ((93 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_076 (t : ℝ)
    (hlo : ((93 / 4) : ℝ) ≤ t) (hhi : t ≤ ((745 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate076
    (fun ht => compactCertificate076_proves ht) ((93 / 4) : ℚ) ((745 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_077 (t : ℝ)
    (hlo : ((745 / 32) : ℝ) ≤ t) (hhi : t ≤ ((373 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate077
    (fun ht => compactCertificate077_proves ht) ((745 / 32) : ℚ) ((373 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_078 (t : ℝ)
    (hlo : ((373 / 16) : ℝ) ≤ t) (hhi : t ≤ ((747 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate078
    (fun ht => compactCertificate078_proves ht) ((373 / 16) : ℚ) ((747 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_079 (t : ℝ)
    (hlo : ((747 / 32) : ℝ) ≤ t) (hhi : t ≤ ((187 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate079
    (fun ht => compactCertificate079_proves ht) ((747 / 32) : ℚ) ((187 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_080 (t : ℝ)
    (hlo : ((187 / 8) : ℝ) ≤ t) (hhi : t ≤ ((749 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate080
    (fun ht => compactCertificate080_proves ht) ((187 / 8) : ℚ) ((749 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_081 (t : ℝ)
    (hlo : ((749 / 32) : ℝ) ≤ t) (hhi : t ≤ ((375 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate081
    (fun ht => compactCertificate081_proves ht) ((749 / 32) : ℚ) ((375 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_082 (t : ℝ)
    (hlo : ((375 / 16) : ℝ) ≤ t) (hhi : t ≤ ((47 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate082
    (fun ht => compactCertificate082_proves ht) ((375 / 16) : ℚ) ((47 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_083 (t : ℝ)
    (hlo : ((47 / 2) : ℝ) ≤ t) (hhi : t ≤ ((189 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate083
    (fun ht => compactCertificate083_proves ht) ((47 / 2) : ℚ) ((189 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_084 (t : ℝ)
    (hlo : ((189 / 8) : ℝ) ≤ t) (hhi : t ≤ ((95 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate084
    (fun ht => compactCertificate084_proves ht) ((189 / 8) : ℚ) ((95 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_085 (t : ℝ)
    (hlo : ((95 / 4) : ℝ) ≤ t) (hhi : t ≤ ((24) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate085
    (fun ht => compactCertificate085_proves ht) ((95 / 4) : ℚ) ((24) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_086 (t : ℝ)
    (hlo : ((24) : ℝ) ≤ t) (hhi : t ≤ ((25) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate086
    (fun ht => compactCertificate086_proves ht) ((24) : ℚ) ((25) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_087 (t : ℝ)
    (hlo : ((25) : ℝ) ≤ t) (hhi : t ≤ ((26) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate087
    (fun ht => compactCertificate087_proves ht) ((25) : ℚ) ((26) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_088 (t : ℝ)
    (hlo : ((26) : ℝ) ≤ t) (hhi : t ≤ ((27) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate088
    (fun ht => compactCertificate088_proves ht) ((26) : ℚ) ((27) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_089 (t : ℝ)
    (hlo : ((27) : ℝ) ≤ t) (hhi : t ≤ ((28) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate089
    (fun ht => compactCertificate089_proves ht) ((27) : ℚ) ((28) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_090 (t : ℝ)
    (hlo : ((28) : ℝ) ≤ t) (hhi : t ≤ ((57 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate090
    (fun ht => compactCertificate090_proves ht) ((28) : ℚ) ((57 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_091 (t : ℝ)
    (hlo : ((57 / 2) : ℝ) ≤ t) (hhi : t ≤ ((115 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate091
    (fun ht => compactCertificate091_proves ht) ((57 / 2) : ℚ) ((115 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_092 (t : ℝ)
    (hlo : ((115 / 4) : ℝ) ≤ t) (hhi : t ≤ ((231 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate092
    (fun ht => compactCertificate092_proves ht) ((115 / 4) : ℚ) ((231 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_093 (t : ℝ)
    (hlo : ((231 / 8) : ℝ) ≤ t) (hhi : t ≤ ((29) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate093
    (fun ht => compactCertificate093_proves ht) ((231 / 8) : ℚ) ((29) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_094 (t : ℝ)
    (hlo : ((29) : ℝ) ≤ t) (hhi : t ≤ ((465 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate094
    (fun ht => compactCertificate094_proves ht) ((29) : ℚ) ((465 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_095 (t : ℝ)
    (hlo : ((465 / 16) : ℝ) ≤ t) (hhi : t ≤ ((931 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate095
    (fun ht => compactCertificate095_proves ht) ((465 / 16) : ℚ) ((931 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_096 (t : ℝ)
    (hlo : ((931 / 32) : ℝ) ≤ t) (hhi : t ≤ ((233 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate096
    (fun ht => compactCertificate096_proves ht) ((931 / 32) : ℚ) ((233 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_097 (t : ℝ)
    (hlo : ((233 / 8) : ℝ) ≤ t) (hhi : t ≤ ((933 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate097
    (fun ht => compactCertificate097_proves ht) ((233 / 8) : ℚ) ((933 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_098 (t : ℝ)
    (hlo : ((933 / 32) : ℝ) ≤ t) (hhi : t ≤ ((467 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate098
    (fun ht => compactCertificate098_proves ht) ((933 / 32) : ℚ) ((467 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_099 (t : ℝ)
    (hlo : ((467 / 16) : ℝ) ≤ t) (hhi : t ≤ ((117 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate099
    (fun ht => compactCertificate099_proves ht) ((467 / 16) : ℚ) ((117 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_100 (t : ℝ)
    (hlo : ((117 / 4) : ℝ) ≤ t) (hhi : t ≤ ((235 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate100
    (fun ht => compactCertificate100_proves ht) ((117 / 4) : ℚ) ((235 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_101 (t : ℝ)
    (hlo : ((235 / 8) : ℝ) ≤ t) (hhi : t ≤ ((59 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate101
    (fun ht => compactCertificate101_proves ht) ((235 / 8) : ℚ) ((59 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_102 (t : ℝ)
    (hlo : ((59 / 2) : ℝ) ≤ t) (hhi : t ≤ ((30) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate102
    (fun ht => compactCertificate102_proves ht) ((59 / 2) : ℚ) ((30) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_103 (t : ℝ)
    (hlo : ((30) : ℝ) ≤ t) (hhi : t ≤ ((61 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate103
    (fun ht => compactCertificate103_proves ht) ((30) : ℚ) ((61 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_104 (t : ℝ)
    (hlo : ((61 / 2) : ℝ) ≤ t) (hhi : t ≤ ((31) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate104
    (fun ht => compactCertificate104_proves ht) ((61 / 2) : ℚ) ((31) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_105 (t : ℝ)
    (hlo : ((31) : ℝ) ≤ t) (hhi : t ≤ ((63 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate105
    (fun ht => compactCertificate105_proves ht) ((31) : ℚ) ((63 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_106 (t : ℝ)
    (hlo : ((63 / 2) : ℝ) ≤ t) (hhi : t ≤ ((32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate106
    (fun ht => compactCertificate106_proves ht) ((63 / 2) : ℚ) ((32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_107 (t : ℝ)
    (hlo : ((32) : ℝ) ≤ t) (hhi : t ≤ ((33) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate107
    (fun ht => compactCertificate107_proves ht) ((32) : ℚ) ((33) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_108 (t : ℝ)
    (hlo : ((33) : ℝ) ≤ t) (hhi : t ≤ ((34) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate108
    (fun ht => compactCertificate108_proves ht) ((33) : ℚ) ((34) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_109 (t : ℝ)
    (hlo : ((34) : ℝ) ≤ t) (hhi : t ≤ ((69 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate109
    (fun ht => compactCertificate109_proves ht) ((34) : ℚ) ((69 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_110 (t : ℝ)
    (hlo : ((69 / 2) : ℝ) ≤ t) (hhi : t ≤ ((35) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate110
    (fun ht => compactCertificate110_proves ht) ((69 / 2) : ℚ) ((35) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_111 (t : ℝ)
    (hlo : ((35) : ℝ) ≤ t) (hhi : t ≤ ((71 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate111
    (fun ht => compactCertificate111_proves ht) ((35) : ℚ) ((71 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_112 (t : ℝ)
    (hlo : ((71 / 2) : ℝ) ≤ t) (hhi : t ≤ ((36) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate112
    (fun ht => compactCertificate112_proves ht) ((71 / 2) : ℚ) ((36) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_113 (t : ℝ)
    (hlo : ((36) : ℝ) ≤ t) (hhi : t ≤ ((145 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate113
    (fun ht => compactCertificate113_proves ht) ((36) : ℚ) ((145 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_114 (t : ℝ)
    (hlo : ((145 / 4) : ℝ) ≤ t) (hhi : t ≤ ((581 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate114
    (fun ht => compactCertificate114_proves ht) ((145 / 4) : ℚ) ((581 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_115 (t : ℝ)
    (hlo : ((581 / 16) : ℝ) ≤ t) (hhi : t ≤ ((291 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate115
    (fun ht => compactCertificate115_proves ht) ((581 / 16) : ℚ) ((291 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_116 (t : ℝ)
    (hlo : ((291 / 8) : ℝ) ≤ t) (hhi : t ≤ ((1165 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate116
    (fun ht => compactCertificate116_proves ht) ((291 / 8) : ℚ) ((1165 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_117 (t : ℝ)
    (hlo : ((1165 / 32) : ℝ) ≤ t) (hhi : t ≤ ((583 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate117
    (fun ht => compactCertificate117_proves ht) ((1165 / 32) : ℚ) ((583 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_118 (t : ℝ)
    (hlo : ((583 / 16) : ℝ) ≤ t) (hhi : t ≤ ((1167 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate118
    (fun ht => compactCertificate118_proves ht) ((583 / 16) : ℚ) ((1167 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_119 (t : ℝ)
    (hlo : ((1167 / 32) : ℝ) ≤ t) (hhi : t ≤ ((73 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate119
    (fun ht => compactCertificate119_proves ht) ((1167 / 32) : ℚ) ((73 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_120 (t : ℝ)
    (hlo : ((73 / 2) : ℝ) ≤ t) (hhi : t ≤ ((585 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate120
    (fun ht => compactCertificate120_proves ht) ((73 / 2) : ℚ) ((585 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_121 (t : ℝ)
    (hlo : ((585 / 16) : ℝ) ≤ t) (hhi : t ≤ ((293 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate121
    (fun ht => compactCertificate121_proves ht) ((585 / 16) : ℚ) ((293 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_122 (t : ℝ)
    (hlo : ((293 / 8) : ℝ) ≤ t) (hhi : t ≤ ((147 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate122
    (fun ht => compactCertificate122_proves ht) ((293 / 8) : ℚ) ((147 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_123 (t : ℝ)
    (hlo : ((147 / 4) : ℝ) ≤ t) (hhi : t ≤ ((37) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate123
    (fun ht => compactCertificate123_proves ht) ((147 / 4) : ℚ) ((37) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_124 (t : ℝ)
    (hlo : ((37) : ℝ) ≤ t) (hhi : t ≤ ((75 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate124
    (fun ht => compactCertificate124_proves ht) ((37) : ℚ) ((75 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_125 (t : ℝ)
    (hlo : ((75 / 2) : ℝ) ≤ t) (hhi : t ≤ ((38) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate125
    (fun ht => compactCertificate125_proves ht) ((75 / 2) : ℚ) ((38) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_126 (t : ℝ)
    (hlo : ((38) : ℝ) ≤ t) (hhi : t ≤ ((39) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate126
    (fun ht => compactCertificate126_proves ht) ((38) : ℚ) ((39) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_127 (t : ℝ)
    (hlo : ((39) : ℝ) ≤ t) (hhi : t ≤ ((40) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate127
    (fun ht => compactCertificate127_proves ht) ((39) : ℚ) ((40) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_128 (t : ℝ)
    (hlo : ((40) : ℝ) ≤ t) (hhi : t ≤ ((81 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate128
    (fun ht => compactCertificate128_proves ht) ((40) : ℚ) ((81 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_129 (t : ℝ)
    (hlo : ((81 / 2) : ℝ) ≤ t) (hhi : t ≤ ((41) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate129
    (fun ht => compactCertificate129_proves ht) ((81 / 2) : ℚ) ((41) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_130 (t : ℝ)
    (hlo : ((41) : ℝ) ≤ t) (hhi : t ≤ ((83 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate130
    (fun ht => compactCertificate130_proves ht) ((41) : ℚ) ((83 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_131 (t : ℝ)
    (hlo : ((83 / 2) : ℝ) ≤ t) (hhi : t ≤ ((42) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate131
    (fun ht => compactCertificate131_proves ht) ((83 / 2) : ℚ) ((42) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_132 (t : ℝ)
    (hlo : ((42) : ℝ) ≤ t) (hhi : t ≤ ((85 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate132
    (fun ht => compactCertificate132_proves ht) ((42) : ℚ) ((85 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_133 (t : ℝ)
    (hlo : ((85 / 2) : ℝ) ≤ t) (hhi : t ≤ ((43) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate133
    (fun ht => compactCertificate133_proves ht) ((85 / 2) : ℚ) ((43) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_134 (t : ℝ)
    (hlo : ((43) : ℝ) ≤ t) (hhi : t ≤ ((44) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate134
    (fun ht => compactCertificate134_proves ht) ((43) : ℚ) ((44) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_135 (t : ℝ)
    (hlo : ((44) : ℝ) ≤ t) (hhi : t ≤ ((45) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate135
    (fun ht => compactCertificate135_proves ht) ((44) : ℚ) ((45) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_136 (t : ℝ)
    (hlo : ((45) : ℝ) ≤ t) (hhi : t ≤ ((46) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate136
    (fun ht => compactCertificate136_proves ht) ((45) : ℚ) ((46) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_137 (t : ℝ)
    (hlo : ((46) : ℝ) ≤ t) (hhi : t ≤ ((47) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate137
    (fun ht => compactCertificate137_proves ht) ((46) : ℚ) ((47) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_138 (t : ℝ)
    (hlo : ((47) : ℝ) ≤ t) (hhi : t ≤ ((95 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate138
    (fun ht => compactCertificate138_proves ht) ((47) : ℚ) ((95 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_139 (t : ℝ)
    (hlo : ((95 / 2) : ℝ) ≤ t) (hhi : t ≤ ((48) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate139
    (fun ht => compactCertificate139_proves ht) ((95 / 2) : ℚ) ((48) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_140 (t : ℝ)
    (hlo : ((48) : ℝ) ≤ t) (hhi : t ≤ ((193 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate140
    (fun ht => compactCertificate140_proves ht) ((48) : ℚ) ((193 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_141 (t : ℝ)
    (hlo : ((193 / 4) : ℝ) ≤ t) (hhi : t ≤ ((97 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate141
    (fun ht => compactCertificate141_proves ht) ((193 / 4) : ℚ) ((97 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_142 (t : ℝ)
    (hlo : ((97 / 2) : ℝ) ≤ t) (hhi : t ≤ ((49) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate142
    (fun ht => compactCertificate142_proves ht) ((97 / 2) : ℚ) ((49) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_143 (t : ℝ)
    (hlo : ((49) : ℝ) ≤ t) (hhi : t ≤ ((50) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate143
    (fun ht => compactCertificate143_proves ht) ((49) : ℚ) ((50) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_144 (t : ℝ)
    (hlo : ((50) : ℝ) ≤ t) (hhi : t ≤ ((51) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate144
    (fun ht => compactCertificate144_proves ht) ((50) : ℚ) ((51) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_145 (t : ℝ)
    (hlo : ((51) : ℝ) ≤ t) (hhi : t ≤ ((103 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate145
    (fun ht => compactCertificate145_proves ht) ((51) : ℚ) ((103 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_146 (t : ℝ)
    (hlo : ((103 / 2) : ℝ) ≤ t) (hhi : t ≤ ((52) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate146
    (fun ht => compactCertificate146_proves ht) ((103 / 2) : ℚ) ((52) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_147 (t : ℝ)
    (hlo : ((52) : ℝ) ≤ t) (hhi : t ≤ ((53) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate147
    (fun ht => compactCertificate147_proves ht) ((52) : ℚ) ((53) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_148 (t : ℝ)
    (hlo : ((53) : ℝ) ≤ t) (hhi : t ≤ ((54) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate148
    (fun ht => compactCertificate148_proves ht) ((53) : ℚ) ((54) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_149 (t : ℝ)
    (hlo : ((54) : ℝ) ≤ t) (hhi : t ≤ ((55) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate149
    (fun ht => compactCertificate149_proves ht) ((54) : ℚ) ((55) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_150 (t : ℝ)
    (hlo : ((55) : ℝ) ≤ t) (hhi : t ≤ ((56) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate150
    (fun ht => compactCertificate150_proves ht) ((55) : ℚ) ((56) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_151 (t : ℝ)
    (hlo : ((56) : ℝ) ≤ t) (hhi : t ≤ ((113 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate151
    (fun ht => compactCertificate151_proves ht) ((56) : ℚ) ((113 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_152 (t : ℝ)
    (hlo : ((113 / 2) : ℝ) ≤ t) (hhi : t ≤ ((57) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate152
    (fun ht => compactCertificate152_proves ht) ((113 / 2) : ℚ) ((57) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_153 (t : ℝ)
    (hlo : ((57) : ℝ) ≤ t) (hhi : t ≤ ((58) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate153
    (fun ht => compactCertificate153_proves ht) ((57) : ℚ) ((58) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_154 (t : ℝ)
    (hlo : ((58) : ℝ) ≤ t) (hhi : t ≤ ((59) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate154
    (fun ht => compactCertificate154_proves ht) ((58) : ℚ) ((59) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_155 (t : ℝ)
    (hlo : ((59) : ℝ) ≤ t) (hhi : t ≤ ((119 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate155
    (fun ht => compactCertificate155_proves ht) ((59) : ℚ) ((119 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_156 (t : ℝ)
    (hlo : ((119 / 2) : ℝ) ≤ t) (hhi : t ≤ ((60) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate156
    (fun ht => compactCertificate156_proves ht) ((119 / 2) : ℚ) ((60) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_157 (t : ℝ)
    (hlo : ((60) : ℝ) ≤ t) (hhi : t ≤ ((61) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate157
    (fun ht => compactCertificate157_proves ht) ((60) : ℚ) ((61) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_158 (t : ℝ)
    (hlo : ((61) : ℝ) ≤ t) (hhi : t ≤ ((123 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate158
    (fun ht => compactCertificate158_proves ht) ((61) : ℚ) ((123 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_159 (t : ℝ)
    (hlo : ((123 / 2) : ℝ) ≤ t) (hhi : t ≤ ((62) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate159
    (fun ht => compactCertificate159_proves ht) ((123 / 2) : ℚ) ((62) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_160 (t : ℝ)
    (hlo : ((62) : ℝ) ≤ t) (hhi : t ≤ ((63) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate160
    (fun ht => compactCertificate160_proves ht) ((62) : ℚ) ((63) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_161 (t : ℝ)
    (hlo : ((63) : ℝ) ≤ t) (hhi : t ≤ ((64) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate161
    (fun ht => compactCertificate161_proves ht) ((63) : ℚ) ((64) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_162 (t : ℝ)
    (hlo : ((64) : ℝ) ≤ t) (hhi : t ≤ ((65) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate162
    (fun ht => compactCertificate162_proves ht) ((64) : ℚ) ((65) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_163 (t : ℝ)
    (hlo : ((65) : ℝ) ≤ t) (hhi : t ≤ ((66) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate163
    (fun ht => compactCertificate163_proves ht) ((65) : ℚ) ((66) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_164 (t : ℝ)
    (hlo : ((66) : ℝ) ≤ t) (hhi : t ≤ ((133 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate164
    (fun ht => compactCertificate164_proves ht) ((66) : ℚ) ((133 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_165 (t : ℝ)
    (hlo : ((133 / 2) : ℝ) ≤ t) (hhi : t ≤ ((67) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate165
    (fun ht => compactCertificate165_proves ht) ((133 / 2) : ℚ) ((67) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_166 (t : ℝ)
    (hlo : ((67) : ℝ) ≤ t) (hhi : t ≤ ((269 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate166
    (fun ht => compactCertificate166_proves ht) ((67) : ℚ) ((269 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_167 (t : ℝ)
    (hlo : ((269 / 4) : ℝ) ≤ t) (hhi : t ≤ ((539 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate167
    (fun ht => compactCertificate167_proves ht) ((269 / 4) : ℚ) ((539 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_168 (t : ℝ)
    (hlo : ((539 / 8) : ℝ) ≤ t) (hhi : t ≤ ((135 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate168
    (fun ht => compactCertificate168_proves ht) ((539 / 8) : ℚ) ((135 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_169 (t : ℝ)
    (hlo : ((135 / 2) : ℝ) ≤ t) (hhi : t ≤ ((541 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate169
    (fun ht => compactCertificate169_proves ht) ((135 / 2) : ℚ) ((541 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_170 (t : ℝ)
    (hlo : ((541 / 8) : ℝ) ≤ t) (hhi : t ≤ ((271 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate170
    (fun ht => compactCertificate170_proves ht) ((541 / 8) : ℚ) ((271 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_171 (t : ℝ)
    (hlo : ((271 / 4) : ℝ) ≤ t) (hhi : t ≤ ((68) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate171
    (fun ht => compactCertificate171_proves ht) ((271 / 4) : ℚ) ((68) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_172 (t : ℝ)
    (hlo : ((68) : ℝ) ≤ t) (hhi : t ≤ ((69) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate172
    (fun ht => compactCertificate172_proves ht) ((68) : ℚ) ((69) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_173 (t : ℝ)
    (hlo : ((69) : ℝ) ≤ t) (hhi : t ≤ ((70) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate173
    (fun ht => compactCertificate173_proves ht) ((69) : ℚ) ((70) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_174 (t : ℝ)
    (hlo : ((70) : ℝ) ≤ t) (hhi : t ≤ ((71) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate174
    (fun ht => compactCertificate174_proves ht) ((70) : ℚ) ((71) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_175 (t : ℝ)
    (hlo : ((71) : ℝ) ≤ t) (hhi : t ≤ ((72) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate175
    (fun ht => compactCertificate175_proves ht) ((71) : ℚ) ((72) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_176 (t : ℝ)
    (hlo : ((72) : ℝ) ≤ t) (hhi : t ≤ ((145 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate176
    (fun ht => compactCertificate176_proves ht) ((72) : ℚ) ((145 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_177 (t : ℝ)
    (hlo : ((145 / 2) : ℝ) ≤ t) (hhi : t ≤ ((73) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate177
    (fun ht => compactCertificate177_proves ht) ((145 / 2) : ℚ) ((73) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_178 (t : ℝ)
    (hlo : ((73) : ℝ) ≤ t) (hhi : t ≤ ((147 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate178
    (fun ht => compactCertificate178_proves ht) ((73) : ℚ) ((147 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_179 (t : ℝ)
    (hlo : ((147 / 2) : ℝ) ≤ t) (hhi : t ≤ ((74) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate179
    (fun ht => compactCertificate179_proves ht) ((147 / 2) : ℚ) ((74) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_180 (t : ℝ)
    (hlo : ((74) : ℝ) ≤ t) (hhi : t ≤ ((75) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate180
    (fun ht => compactCertificate180_proves ht) ((74) : ℚ) ((75) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_181 (t : ℝ)
    (hlo : ((75) : ℝ) ≤ t) (hhi : t ≤ ((76) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate181
    (fun ht => compactCertificate181_proves ht) ((75) : ℚ) ((76) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_182 (t : ℝ)
    (hlo : ((76) : ℝ) ≤ t) (hhi : t ≤ ((77) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate182
    (fun ht => compactCertificate182_proves ht) ((76) : ℚ) ((77) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_183 (t : ℝ)
    (hlo : ((77) : ℝ) ≤ t) (hhi : t ≤ ((78) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate183
    (fun ht => compactCertificate183_proves ht) ((77) : ℚ) ((78) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_184 (t : ℝ)
    (hlo : ((78) : ℝ) ≤ t) (hhi : t ≤ ((79) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate184
    (fun ht => compactCertificate184_proves ht) ((78) : ℚ) ((79) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_185 (t : ℝ)
    (hlo : ((79) : ℝ) ≤ t) (hhi : t ≤ ((80) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate185
    (fun ht => compactCertificate185_proves ht) ((79) : ℚ) ((80) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_186 (t : ℝ)
    (hlo : ((80) : ℝ) ≤ t) (hhi : t ≤ ((161 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate186
    (fun ht => compactCertificate186_proves ht) ((80) : ℚ) ((161 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_187 (t : ℝ)
    (hlo : ((161 / 2) : ℝ) ≤ t) (hhi : t ≤ ((81) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate187
    (fun ht => compactCertificate187_proves ht) ((161 / 2) : ℚ) ((81) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_188 (t : ℝ)
    (hlo : ((81) : ℝ) ≤ t) (hhi : t ≤ ((163 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate188
    (fun ht => compactCertificate188_proves ht) ((81) : ℚ) ((163 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_189 (t : ℝ)
    (hlo : ((163 / 2) : ℝ) ≤ t) (hhi : t ≤ ((82) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate189
    (fun ht => compactCertificate189_proves ht) ((163 / 2) : ℚ) ((82) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_190 (t : ℝ)
    (hlo : ((82) : ℝ) ≤ t) (hhi : t ≤ ((83) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate190
    (fun ht => compactCertificate190_proves ht) ((82) : ℚ) ((83) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_191 (t : ℝ)
    (hlo : ((83) : ℝ) ≤ t) (hhi : t ≤ ((84) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate191
    (fun ht => compactCertificate191_proves ht) ((83) : ℚ) ((84) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_192 (t : ℝ)
    (hlo : ((84) : ℝ) ≤ t) (hhi : t ≤ ((85) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate192
    (fun ht => compactCertificate192_proves ht) ((84) : ℚ) ((85) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_193 (t : ℝ)
    (hlo : ((85) : ℝ) ≤ t) (hhi : t ≤ ((86) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate193
    (fun ht => compactCertificate193_proves ht) ((85) : ℚ) ((86) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_194 (t : ℝ)
    (hlo : ((86) : ℝ) ≤ t) (hhi : t ≤ ((87) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate194
    (fun ht => compactCertificate194_proves ht) ((86) : ℚ) ((87) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_195 (t : ℝ)
    (hlo : ((87) : ℝ) ≤ t) (hhi : t ≤ ((88) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate195
    (fun ht => compactCertificate195_proves ht) ((87) : ℚ) ((88) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_196 (t : ℝ)
    (hlo : ((88) : ℝ) ≤ t) (hhi : t ≤ ((89) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate196
    (fun ht => compactCertificate196_proves ht) ((88) : ℚ) ((89) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_197 (t : ℝ)
    (hlo : ((89) : ℝ) ≤ t) (hhi : t ≤ ((90) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate197
    (fun ht => compactCertificate197_proves ht) ((89) : ℚ) ((90) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_198 (t : ℝ)
    (hlo : ((90) : ℝ) ≤ t) (hhi : t ≤ ((91) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate198
    (fun ht => compactCertificate198_proves ht) ((90) : ℚ) ((91) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_199 (t : ℝ)
    (hlo : ((91) : ℝ) ≤ t) (hhi : t ≤ ((183 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate199
    (fun ht => compactCertificate199_proves ht) ((91) : ℚ) ((183 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_200 (t : ℝ)
    (hlo : ((183 / 2) : ℝ) ≤ t) (hhi : t ≤ ((92) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate200
    (fun ht => compactCertificate200_proves ht) ((183 / 2) : ℚ) ((92) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_201 (t : ℝ)
    (hlo : ((92) : ℝ) ≤ t) (hhi : t ≤ ((369 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate201
    (fun ht => compactCertificate201_proves ht) ((92) : ℚ) ((369 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_202 (t : ℝ)
    (hlo : ((369 / 4) : ℝ) ≤ t) (hhi : t ≤ ((739 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate202
    (fun ht => compactCertificate202_proves ht) ((369 / 4) : ℚ) ((739 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_203 (t : ℝ)
    (hlo : ((739 / 8) : ℝ) ≤ t) (hhi : t ≤ ((2957 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate203
    (fun ht => compactCertificate203_proves ht) ((739 / 8) : ℚ) ((2957 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_204 (t : ℝ)
    (hlo : ((2957 / 32) : ℝ) ≤ t) (hhi : t ≤ ((1479 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate204
    (fun ht => compactCertificate204_proves ht) ((2957 / 32) : ℚ) ((1479 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_205 (t : ℝ)
    (hlo : ((1479 / 16) : ℝ) ≤ t) (hhi : t ≤ ((2959 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate205
    (fun ht => compactCertificate205_proves ht) ((1479 / 16) : ℚ) ((2959 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_206 (t : ℝ)
    (hlo : ((2959 / 32) : ℝ) ≤ t) (hhi : t ≤ ((185 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate206
    (fun ht => compactCertificate206_proves ht) ((2959 / 32) : ℚ) ((185 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_207 (t : ℝ)
    (hlo : ((185 / 2) : ℝ) ≤ t) (hhi : t ≤ ((2961 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate207
    (fun ht => compactCertificate207_proves ht) ((185 / 2) : ℚ) ((2961 / 32) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_208 (t : ℝ)
    (hlo : ((2961 / 32) : ℝ) ≤ t) (hhi : t ≤ ((1481 / 16) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate208
    (fun ht => compactCertificate208_proves ht) ((2961 / 32) : ℚ) ((1481 / 16) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_209 (t : ℝ)
    (hlo : ((1481 / 16) : ℝ) ≤ t) (hhi : t ≤ ((741 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate209
    (fun ht => compactCertificate209_proves ht) ((1481 / 16) : ℚ) ((741 / 8) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_210 (t : ℝ)
    (hlo : ((741 / 8) : ℝ) ≤ t) (hhi : t ≤ ((371 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate210
    (fun ht => compactCertificate210_proves ht) ((741 / 8) : ℚ) ((371 / 4) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_211 (t : ℝ)
    (hlo : ((371 / 4) : ℝ) ≤ t) (hhi : t ≤ ((93) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate211
    (fun ht => compactCertificate211_proves ht) ((371 / 4) : ℚ) ((93) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_212 (t : ℝ)
    (hlo : ((93) : ℝ) ≤ t) (hhi : t ≤ ((94) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate212
    (fun ht => compactCertificate212_proves ht) ((93) : ℚ) ((94) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_213 (t : ℝ)
    (hlo : ((94) : ℝ) ≤ t) (hhi : t ≤ ((95) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate213
    (fun ht => compactCertificate213_proves ht) ((94) : ℚ) ((95) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_214 (t : ℝ)
    (hlo : ((95) : ℝ) ≤ t) (hhi : t ≤ ((96) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate214
    (fun ht => compactCertificate214_proves ht) ((95) : ℚ) ((96) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_215 (t : ℝ)
    (hlo : ((96) : ℝ) ≤ t) (hhi : t ≤ ((97) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate215
    (fun ht => compactCertificate215_proves ht) ((96) : ℚ) ((97) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_216 (t : ℝ)
    (hlo : ((97) : ℝ) ≤ t) (hhi : t ≤ ((195 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate216
    (fun ht => compactCertificate216_proves ht) ((97) : ℚ) ((195 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_217 (t : ℝ)
    (hlo : ((195 / 2) : ℝ) ≤ t) (hhi : t ≤ ((98) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate217
    (fun ht => compactCertificate217_proves ht) ((195 / 2) : ℚ) ((98) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_218 (t : ℝ)
    (hlo : ((98) : ℝ) ≤ t) (hhi : t ≤ ((197 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate218
    (fun ht => compactCertificate218_proves ht) ((98) : ℚ) ((197 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_219 (t : ℝ)
    (hlo : ((197 / 2) : ℝ) ≤ t) (hhi : t ≤ ((99) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate219
    (fun ht => compactCertificate219_proves ht) ((197 / 2) : ℚ) ((99) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_220 (t : ℝ)
    (hlo : ((99) : ℝ) ≤ t) (hhi : t ≤ ((100) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate220
    (fun ht => compactCertificate220_proves ht) ((99) : ℚ) ((100) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_221 (t : ℝ)
    (hlo : ((100) : ℝ) ≤ t) (hhi : t ≤ ((101) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate221
    (fun ht => compactCertificate221_proves ht) ((100) : ℚ) ((101) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_222 (t : ℝ)
    (hlo : ((101) : ℝ) ≤ t) (hhi : t ≤ ((102) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate222
    (fun ht => compactCertificate222_proves ht) ((101) : ℚ) ((102) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_223 (t : ℝ)
    (hlo : ((102) : ℝ) ≤ t) (hhi : t ≤ ((103) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate223
    (fun ht => compactCertificate223_proves ht) ((102) : ℚ) ((103) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_224 (t : ℝ)
    (hlo : ((103) : ℝ) ≤ t) (hhi : t ≤ ((104) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate224
    (fun ht => compactCertificate224_proves ht) ((103) : ℚ) ((104) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_225 (t : ℝ)
    (hlo : ((104) : ℝ) ≤ t) (hhi : t ≤ ((209 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate225
    (fun ht => compactCertificate225_proves ht) ((104) : ℚ) ((209 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_226 (t : ℝ)
    (hlo : ((209 / 2) : ℝ) ≤ t) (hhi : t ≤ ((105) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate226
    (fun ht => compactCertificate226_proves ht) ((209 / 2) : ℚ) ((105) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_227 (t : ℝ)
    (hlo : ((105) : ℝ) ≤ t) (hhi : t ≤ ((211 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate227
    (fun ht => compactCertificate227_proves ht) ((105) : ℚ) ((211 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_228 (t : ℝ)
    (hlo : ((211 / 2) : ℝ) ≤ t) (hhi : t ≤ ((106) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate228
    (fun ht => compactCertificate228_proves ht) ((211 / 2) : ℚ) ((106) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_229 (t : ℝ)
    (hlo : ((106) : ℝ) ≤ t) (hhi : t ≤ ((107) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate229
    (fun ht => compactCertificate229_proves ht) ((106) : ℚ) ((107) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_230 (t : ℝ)
    (hlo : ((107) : ℝ) ≤ t) (hhi : t ≤ ((108) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate230
    (fun ht => compactCertificate230_proves ht) ((107) : ℚ) ((108) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_231 (t : ℝ)
    (hlo : ((108) : ℝ) ≤ t) (hhi : t ≤ ((109) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate231
    (fun ht => compactCertificate231_proves ht) ((108) : ℚ) ((109) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_232 (t : ℝ)
    (hlo : ((109) : ℝ) ≤ t) (hhi : t ≤ ((110) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate232
    (fun ht => compactCertificate232_proves ht) ((109) : ℚ) ((110) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_233 (t : ℝ)
    (hlo : ((110) : ℝ) ≤ t) (hhi : t ≤ ((111) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate233
    (fun ht => compactCertificate233_proves ht) ((110) : ℚ) ((111) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_234 (t : ℝ)
    (hlo : ((111) : ℝ) ≤ t) (hhi : t ≤ ((112) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate234
    (fun ht => compactCertificate234_proves ht) ((111) : ℚ) ((112) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_235 (t : ℝ)
    (hlo : ((112) : ℝ) ≤ t) (hhi : t ≤ ((113) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate235
    (fun ht => compactCertificate235_proves ht) ((112) : ℚ) ((113) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_236 (t : ℝ)
    (hlo : ((113) : ℝ) ≤ t) (hhi : t ≤ ((114) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate236
    (fun ht => compactCertificate236_proves ht) ((113) : ℚ) ((114) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_237 (t : ℝ)
    (hlo : ((114) : ℝ) ≤ t) (hhi : t ≤ ((115) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate237
    (fun ht => compactCertificate237_proves ht) ((114) : ℚ) ((115) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_238 (t : ℝ)
    (hlo : ((115) : ℝ) ≤ t) (hhi : t ≤ ((116) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate238
    (fun ht => compactCertificate238_proves ht) ((115) : ℚ) ((116) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_239 (t : ℝ)
    (hlo : ((116) : ℝ) ≤ t) (hhi : t ≤ ((233 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate239
    (fun ht => compactCertificate239_proves ht) ((116) : ℚ) ((233 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_240 (t : ℝ)
    (hlo : ((233 / 2) : ℝ) ≤ t) (hhi : t ≤ ((117) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate240
    (fun ht => compactCertificate240_proves ht) ((233 / 2) : ℚ) ((117) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_241 (t : ℝ)
    (hlo : ((117) : ℝ) ≤ t) (hhi : t ≤ ((235 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate241
    (fun ht => compactCertificate241_proves ht) ((117) : ℚ) ((235 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_242 (t : ℝ)
    (hlo : ((235 / 2) : ℝ) ≤ t) (hhi : t ≤ ((118) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate242
    (fun ht => compactCertificate242_proves ht) ((235 / 2) : ℚ) ((118) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_243 (t : ℝ)
    (hlo : ((118) : ℝ) ≤ t) (hhi : t ≤ ((119) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate243
    (fun ht => compactCertificate243_proves ht) ((118) : ℚ) ((119) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_244 (t : ℝ)
    (hlo : ((119) : ℝ) ≤ t) (hhi : t ≤ ((120) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate244
    (fun ht => compactCertificate244_proves ht) ((119) : ℚ) ((120) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_245 (t : ℝ)
    (hlo : ((120) : ℝ) ≤ t) (hhi : t ≤ ((121) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate245
    (fun ht => compactCertificate245_proves ht) ((120) : ℚ) ((121) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_246 (t : ℝ)
    (hlo : ((121) : ℝ) ≤ t) (hhi : t ≤ ((122) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate246
    (fun ht => compactCertificate246_proves ht) ((121) : ℚ) ((122) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_247 (t : ℝ)
    (hlo : ((122) : ℝ) ≤ t) (hhi : t ≤ ((123) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate247
    (fun ht => compactCertificate247_proves ht) ((122) : ℚ) ((123) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_248 (t : ℝ)
    (hlo : ((123) : ℝ) ≤ t) (hhi : t ≤ ((124) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate248
    (fun ht => compactCertificate248_proves ht) ((123) : ℚ) ((124) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_249 (t : ℝ)
    (hlo : ((124) : ℝ) ≤ t) (hhi : t ≤ ((125) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate249
    (fun ht => compactCertificate249_proves ht) ((124) : ℚ) ((125) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_250 (t : ℝ)
    (hlo : ((125) : ℝ) ≤ t) (hhi : t ≤ ((126) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate250
    (fun ht => compactCertificate250_proves ht) ((125) : ℚ) ((126) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_251 (t : ℝ)
    (hlo : ((126) : ℝ) ≤ t) (hhi : t ≤ ((127) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate251
    (fun ht => compactCertificate251_proves ht) ((126) : ℚ) ((127) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_252 (t : ℝ)
    (hlo : ((127) : ℝ) ≤ t) (hhi : t ≤ ((128) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate252
    (fun ht => compactCertificate252_proves ht) ((127) : ℚ) ((128) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_253 (t : ℝ)
    (hlo : ((128) : ℝ) ≤ t) (hhi : t ≤ ((129) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate253
    (fun ht => compactCertificate253_proves ht) ((128) : ℚ) ((129) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_254 (t : ℝ)
    (hlo : ((129) : ℝ) ≤ t) (hhi : t ≤ ((130) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate254
    (fun ht => compactCertificate254_proves ht) ((129) : ℚ) ((130) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_255 (t : ℝ)
    (hlo : ((130) : ℝ) ≤ t) (hhi : t ≤ ((131) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate255
    (fun ht => compactCertificate255_proves ht) ((130) : ℚ) ((131) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_256 (t : ℝ)
    (hlo : ((131) : ℝ) ≤ t) (hhi : t ≤ ((132) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate256
    (fun ht => compactCertificate256_proves ht) ((131) : ℚ) ((132) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_257 (t : ℝ)
    (hlo : ((132) : ℝ) ≤ t) (hhi : t ≤ ((133) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate257
    (fun ht => compactCertificate257_proves ht) ((132) : ℚ) ((133) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_258 (t : ℝ)
    (hlo : ((133) : ℝ) ≤ t) (hhi : t ≤ ((134) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate258
    (fun ht => compactCertificate258_proves ht) ((133) : ℚ) ((134) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_259 (t : ℝ)
    (hlo : ((134) : ℝ) ≤ t) (hhi : t ≤ ((135) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate259
    (fun ht => compactCertificate259_proves ht) ((134) : ℚ) ((135) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_260 (t : ℝ)
    (hlo : ((135) : ℝ) ≤ t) (hhi : t ≤ ((271 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate260
    (fun ht => compactCertificate260_proves ht) ((135) : ℚ) ((271 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_261 (t : ℝ)
    (hlo : ((271 / 2) : ℝ) ≤ t) (hhi : t ≤ ((136) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate261
    (fun ht => compactCertificate261_proves ht) ((271 / 2) : ℚ) ((136) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_262 (t : ℝ)
    (hlo : ((136) : ℝ) ≤ t) (hhi : t ≤ ((137) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate262
    (fun ht => compactCertificate262_proves ht) ((136) : ℚ) ((137) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_263 (t : ℝ)
    (hlo : ((137) : ℝ) ≤ t) (hhi : t ≤ ((138) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate263
    (fun ht => compactCertificate263_proves ht) ((137) : ℚ) ((138) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_264 (t : ℝ)
    (hlo : ((138) : ℝ) ≤ t) (hhi : t ≤ ((139) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate264
    (fun ht => compactCertificate264_proves ht) ((138) : ℚ) ((139) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_265 (t : ℝ)
    (hlo : ((139) : ℝ) ≤ t) (hhi : t ≤ ((140) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate265
    (fun ht => compactCertificate265_proves ht) ((139) : ℚ) ((140) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_266 (t : ℝ)
    (hlo : ((140) : ℝ) ≤ t) (hhi : t ≤ ((141) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate266
    (fun ht => compactCertificate266_proves ht) ((140) : ℚ) ((141) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_267 (t : ℝ)
    (hlo : ((141) : ℝ) ≤ t) (hhi : t ≤ ((142) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate267
    (fun ht => compactCertificate267_proves ht) ((141) : ℚ) ((142) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_268 (t : ℝ)
    (hlo : ((142) : ℝ) ≤ t) (hhi : t ≤ ((143) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate268
    (fun ht => compactCertificate268_proves ht) ((142) : ℚ) ((143) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_269 (t : ℝ)
    (hlo : ((143) : ℝ) ≤ t) (hhi : t ≤ ((144) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate269
    (fun ht => compactCertificate269_proves ht) ((143) : ℚ) ((144) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_270 (t : ℝ)
    (hlo : ((144) : ℝ) ≤ t) (hhi : t ≤ ((145) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate270
    (fun ht => compactCertificate270_proves ht) ((144) : ℚ) ((145) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_271 (t : ℝ)
    (hlo : ((145) : ℝ) ≤ t) (hhi : t ≤ ((146) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate271
    (fun ht => compactCertificate271_proves ht) ((145) : ℚ) ((146) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_272 (t : ℝ)
    (hlo : ((146) : ℝ) ≤ t) (hhi : t ≤ ((147) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate272
    (fun ht => compactCertificate272_proves ht) ((146) : ℚ) ((147) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_273 (t : ℝ)
    (hlo : ((147) : ℝ) ≤ t) (hhi : t ≤ ((148) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate273
    (fun ht => compactCertificate273_proves ht) ((147) : ℚ) ((148) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_274 (t : ℝ)
    (hlo : ((148) : ℝ) ≤ t) (hhi : t ≤ ((149) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate274
    (fun ht => compactCertificate274_proves ht) ((148) : ℚ) ((149) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_275 (t : ℝ)
    (hlo : ((149) : ℝ) ≤ t) (hhi : t ≤ ((150) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate275
    (fun ht => compactCertificate275_proves ht) ((149) : ℚ) ((150) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_276 (t : ℝ)
    (hlo : ((150) : ℝ) ≤ t) (hhi : t ≤ ((151) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate276
    (fun ht => compactCertificate276_proves ht) ((150) : ℚ) ((151) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_277 (t : ℝ)
    (hlo : ((151) : ℝ) ≤ t) (hhi : t ≤ ((152) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate277
    (fun ht => compactCertificate277_proves ht) ((151) : ℚ) ((152) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_278 (t : ℝ)
    (hlo : ((152) : ℝ) ≤ t) (hhi : t ≤ ((153) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate278
    (fun ht => compactCertificate278_proves ht) ((152) : ℚ) ((153) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_279 (t : ℝ)
    (hlo : ((153) : ℝ) ≤ t) (hhi : t ≤ ((154) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate279
    (fun ht => compactCertificate279_proves ht) ((153) : ℚ) ((154) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_280 (t : ℝ)
    (hlo : ((154) : ℝ) ≤ t) (hhi : t ≤ ((155) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate280
    (fun ht => compactCertificate280_proves ht) ((154) : ℚ) ((155) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_281 (t : ℝ)
    (hlo : ((155) : ℝ) ≤ t) (hhi : t ≤ ((156) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate281
    (fun ht => compactCertificate281_proves ht) ((155) : ℚ) ((156) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_282 (t : ℝ)
    (hlo : ((156) : ℝ) ≤ t) (hhi : t ≤ ((157) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate282
    (fun ht => compactCertificate282_proves ht) ((156) : ℚ) ((157) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_283 (t : ℝ)
    (hlo : ((157) : ℝ) ≤ t) (hhi : t ≤ ((158) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate283
    (fun ht => compactCertificate283_proves ht) ((157) : ℚ) ((158) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_284 (t : ℝ)
    (hlo : ((158) : ℝ) ≤ t) (hhi : t ≤ ((159) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate284
    (fun ht => compactCertificate284_proves ht) ((158) : ℚ) ((159) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_285 (t : ℝ)
    (hlo : ((159) : ℝ) ≤ t) (hhi : t ≤ ((160) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate285
    (fun ht => compactCertificate285_proves ht) ((159) : ℚ) ((160) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_286 (t : ℝ)
    (hlo : ((160) : ℝ) ≤ t) (hhi : t ≤ ((161) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate286
    (fun ht => compactCertificate286_proves ht) ((160) : ℚ) ((161) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_287 (t : ℝ)
    (hlo : ((161) : ℝ) ≤ t) (hhi : t ≤ ((162) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate287
    (fun ht => compactCertificate287_proves ht) ((161) : ℚ) ((162) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_288 (t : ℝ)
    (hlo : ((162) : ℝ) ≤ t) (hhi : t ≤ ((163) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate288
    (fun ht => compactCertificate288_proves ht) ((162) : ℚ) ((163) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_289 (t : ℝ)
    (hlo : ((163) : ℝ) ≤ t) (hhi : t ≤ ((164) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate289
    (fun ht => compactCertificate289_proves ht) ((163) : ℚ) ((164) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_290 (t : ℝ)
    (hlo : ((164) : ℝ) ≤ t) (hhi : t ≤ ((165) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate290
    (fun ht => compactCertificate290_proves ht) ((164) : ℚ) ((165) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_291 (t : ℝ)
    (hlo : ((165) : ℝ) ≤ t) (hhi : t ≤ ((166) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate291
    (fun ht => compactCertificate291_proves ht) ((165) : ℚ) ((166) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_292 (t : ℝ)
    (hlo : ((166) : ℝ) ≤ t) (hhi : t ≤ ((333 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate292
    (fun ht => compactCertificate292_proves ht) ((166) : ℚ) ((333 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_293 (t : ℝ)
    (hlo : ((333 / 2) : ℝ) ≤ t) (hhi : t ≤ ((167) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate293
    (fun ht => compactCertificate293_proves ht) ((333 / 2) : ℚ) ((167) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_294 (t : ℝ)
    (hlo : ((167) : ℝ) ≤ t) (hhi : t ≤ ((168) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate294
    (fun ht => compactCertificate294_proves ht) ((167) : ℚ) ((168) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_295 (t : ℝ)
    (hlo : ((168) : ℝ) ≤ t) (hhi : t ≤ ((169) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate295
    (fun ht => compactCertificate295_proves ht) ((168) : ℚ) ((169) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_296 (t : ℝ)
    (hlo : ((169) : ℝ) ≤ t) (hhi : t ≤ ((170) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate296
    (fun ht => compactCertificate296_proves ht) ((169) : ℚ) ((170) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_297 (t : ℝ)
    (hlo : ((170) : ℝ) ≤ t) (hhi : t ≤ ((171) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate297
    (fun ht => compactCertificate297_proves ht) ((170) : ℚ) ((171) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_298 (t : ℝ)
    (hlo : ((171) : ℝ) ≤ t) (hhi : t ≤ ((172) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate298
    (fun ht => compactCertificate298_proves ht) ((171) : ℚ) ((172) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_299 (t : ℝ)
    (hlo : ((172) : ℝ) ≤ t) (hhi : t ≤ ((173) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate299
    (fun ht => compactCertificate299_proves ht) ((172) : ℚ) ((173) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_300 (t : ℝ)
    (hlo : ((173) : ℝ) ≤ t) (hhi : t ≤ ((174) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate300
    (fun ht => compactCertificate300_proves ht) ((173) : ℚ) ((174) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_301 (t : ℝ)
    (hlo : ((174) : ℝ) ≤ t) (hhi : t ≤ ((175) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate301
    (fun ht => compactCertificate301_proves ht) ((174) : ℚ) ((175) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_302 (t : ℝ)
    (hlo : ((175) : ℝ) ≤ t) (hhi : t ≤ ((176) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate302
    (fun ht => compactCertificate302_proves ht) ((175) : ℚ) ((176) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_303 (t : ℝ)
    (hlo : ((176) : ℝ) ≤ t) (hhi : t ≤ ((177) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate303
    (fun ht => compactCertificate303_proves ht) ((176) : ℚ) ((177) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_304 (t : ℝ)
    (hlo : ((177) : ℝ) ≤ t) (hhi : t ≤ ((178) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate304
    (fun ht => compactCertificate304_proves ht) ((177) : ℚ) ((178) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_305 (t : ℝ)
    (hlo : ((178) : ℝ) ≤ t) (hhi : t ≤ ((179) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate305
    (fun ht => compactCertificate305_proves ht) ((178) : ℚ) ((179) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_306 (t : ℝ)
    (hlo : ((179) : ℝ) ≤ t) (hhi : t ≤ ((180) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate306
    (fun ht => compactCertificate306_proves ht) ((179) : ℚ) ((180) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_307 (t : ℝ)
    (hlo : ((180) : ℝ) ≤ t) (hhi : t ≤ ((181) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate307
    (fun ht => compactCertificate307_proves ht) ((180) : ℚ) ((181) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_308 (t : ℝ)
    (hlo : ((181) : ℝ) ≤ t) (hhi : t ≤ ((182) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate308
    (fun ht => compactCertificate308_proves ht) ((181) : ℚ) ((182) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_309 (t : ℝ)
    (hlo : ((182) : ℝ) ≤ t) (hhi : t ≤ ((183) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate309
    (fun ht => compactCertificate309_proves ht) ((182) : ℚ) ((183) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_310 (t : ℝ)
    (hlo : ((183) : ℝ) ≤ t) (hhi : t ≤ ((184) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate310
    (fun ht => compactCertificate310_proves ht) ((183) : ℚ) ((184) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_311 (t : ℝ)
    (hlo : ((184) : ℝ) ≤ t) (hhi : t ≤ ((185) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate311
    (fun ht => compactCertificate311_proves ht) ((184) : ℚ) ((185) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_312 (t : ℝ)
    (hlo : ((185) : ℝ) ≤ t) (hhi : t ≤ ((186) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate312
    (fun ht => compactCertificate312_proves ht) ((185) : ℚ) ((186) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_313 (t : ℝ)
    (hlo : ((186) : ℝ) ≤ t) (hhi : t ≤ ((187) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate313
    (fun ht => compactCertificate313_proves ht) ((186) : ℚ) ((187) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_314 (t : ℝ)
    (hlo : ((187) : ℝ) ≤ t) (hhi : t ≤ ((188) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate314
    (fun ht => compactCertificate314_proves ht) ((187) : ℚ) ((188) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_315 (t : ℝ)
    (hlo : ((188) : ℝ) ≤ t) (hhi : t ≤ ((189) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate315
    (fun ht => compactCertificate315_proves ht) ((188) : ℚ) ((189) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_316 (t : ℝ)
    (hlo : ((189) : ℝ) ≤ t) (hhi : t ≤ ((190) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate316
    (fun ht => compactCertificate316_proves ht) ((189) : ℚ) ((190) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_317 (t : ℝ)
    (hlo : ((190) : ℝ) ≤ t) (hhi : t ≤ ((191) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate317
    (fun ht => compactCertificate317_proves ht) ((190) : ℚ) ((191) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_318 (t : ℝ)
    (hlo : ((191) : ℝ) ≤ t) (hhi : t ≤ ((383 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate318
    (fun ht => compactCertificate318_proves ht) ((191) : ℚ) ((383 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_319 (t : ℝ)
    (hlo : ((383 / 2) : ℝ) ≤ t) (hhi : t ≤ ((192) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate319
    (fun ht => compactCertificate319_proves ht) ((383 / 2) : ℚ) ((192) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_320 (t : ℝ)
    (hlo : ((192) : ℝ) ≤ t) (hhi : t ≤ ((193) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate320
    (fun ht => compactCertificate320_proves ht) ((192) : ℚ) ((193) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_321 (t : ℝ)
    (hlo : ((193) : ℝ) ≤ t) (hhi : t ≤ ((194) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate321
    (fun ht => compactCertificate321_proves ht) ((193) : ℚ) ((194) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_322 (t : ℝ)
    (hlo : ((194) : ℝ) ≤ t) (hhi : t ≤ ((195) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate322
    (fun ht => compactCertificate322_proves ht) ((194) : ℚ) ((195) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_323 (t : ℝ)
    (hlo : ((195) : ℝ) ≤ t) (hhi : t ≤ ((196) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate323
    (fun ht => compactCertificate323_proves ht) ((195) : ℚ) ((196) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_324 (t : ℝ)
    (hlo : ((196) : ℝ) ≤ t) (hhi : t ≤ ((197) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate324
    (fun ht => compactCertificate324_proves ht) ((196) : ℚ) ((197) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_325 (t : ℝ)
    (hlo : ((197) : ℝ) ≤ t) (hhi : t ≤ ((198) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate325
    (fun ht => compactCertificate325_proves ht) ((197) : ℚ) ((198) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_326 (t : ℝ)
    (hlo : ((198) : ℝ) ≤ t) (hhi : t ≤ ((199) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate326
    (fun ht => compactCertificate326_proves ht) ((198) : ℚ) ((199) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_327 (t : ℝ)
    (hlo : ((199) : ℝ) ≤ t) (hhi : t ≤ ((200) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate327
    (fun ht => compactCertificate327_proves ht) ((199) : ℚ) ((200) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_328 (t : ℝ)
    (hlo : ((200) : ℝ) ≤ t) (hhi : t ≤ ((201) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate328
    (fun ht => compactCertificate328_proves ht) ((200) : ℚ) ((201) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_329 (t : ℝ)
    (hlo : ((201) : ℝ) ≤ t) (hhi : t ≤ ((202) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate329
    (fun ht => compactCertificate329_proves ht) ((201) : ℚ) ((202) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_330 (t : ℝ)
    (hlo : ((202) : ℝ) ≤ t) (hhi : t ≤ ((203) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate330
    (fun ht => compactCertificate330_proves ht) ((202) : ℚ) ((203) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_331 (t : ℝ)
    (hlo : ((203) : ℝ) ≤ t) (hhi : t ≤ ((204) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate331
    (fun ht => compactCertificate331_proves ht) ((203) : ℚ) ((204) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_332 (t : ℝ)
    (hlo : ((204) : ℝ) ≤ t) (hhi : t ≤ ((205) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate332
    (fun ht => compactCertificate332_proves ht) ((204) : ℚ) ((205) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_333 (t : ℝ)
    (hlo : ((205) : ℝ) ≤ t) (hhi : t ≤ ((206) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate333
    (fun ht => compactCertificate333_proves ht) ((205) : ℚ) ((206) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_334 (t : ℝ)
    (hlo : ((206) : ℝ) ≤ t) (hhi : t ≤ ((207) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate334
    (fun ht => compactCertificate334_proves ht) ((206) : ℚ) ((207) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_335 (t : ℝ)
    (hlo : ((207) : ℝ) ≤ t) (hhi : t ≤ ((208) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate335
    (fun ht => compactCertificate335_proves ht) ((207) : ℚ) ((208) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_336 (t : ℝ)
    (hlo : ((208) : ℝ) ≤ t) (hhi : t ≤ ((209) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate336
    (fun ht => compactCertificate336_proves ht) ((208) : ℚ) ((209) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_337 (t : ℝ)
    (hlo : ((209) : ℝ) ≤ t) (hhi : t ≤ ((210) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate337
    (fun ht => compactCertificate337_proves ht) ((209) : ℚ) ((210) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_338 (t : ℝ)
    (hlo : ((210) : ℝ) ≤ t) (hhi : t ≤ ((211) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate338
    (fun ht => compactCertificate338_proves ht) ((210) : ℚ) ((211) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_339 (t : ℝ)
    (hlo : ((211) : ℝ) ≤ t) (hhi : t ≤ ((212) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate339
    (fun ht => compactCertificate339_proves ht) ((211) : ℚ) ((212) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_340 (t : ℝ)
    (hlo : ((212) : ℝ) ≤ t) (hhi : t ≤ ((213) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate340
    (fun ht => compactCertificate340_proves ht) ((212) : ℚ) ((213) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_341 (t : ℝ)
    (hlo : ((213) : ℝ) ≤ t) (hhi : t ≤ ((214) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate341
    (fun ht => compactCertificate341_proves ht) ((213) : ℚ) ((214) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_342 (t : ℝ)
    (hlo : ((214) : ℝ) ≤ t) (hhi : t ≤ ((215) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate342
    (fun ht => compactCertificate342_proves ht) ((214) : ℚ) ((215) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_343 (t : ℝ)
    (hlo : ((215) : ℝ) ≤ t) (hhi : t ≤ ((216) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate343
    (fun ht => compactCertificate343_proves ht) ((215) : ℚ) ((216) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_344 (t : ℝ)
    (hlo : ((216) : ℝ) ≤ t) (hhi : t ≤ ((433 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate344
    (fun ht => compactCertificate344_proves ht) ((216) : ℚ) ((433 / 2) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_345 (t : ℝ)
    (hlo : ((433 / 2) : ℝ) ≤ t) (hhi : t ≤ ((217) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate345
    (fun ht => compactCertificate345_proves ht) ((433 / 2) : ℚ) ((217) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_346 (t : ℝ)
    (hlo : ((217) : ℝ) ≤ t) (hhi : t ≤ ((218) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate346
    (fun ht => compactCertificate346_proves ht) ((217) : ℚ) ((218) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_347 (t : ℝ)
    (hlo : ((218) : ℝ) ≤ t) (hhi : t ≤ ((219) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate347
    (fun ht => compactCertificate347_proves ht) ((218) : ℚ) ((219) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_348 (t : ℝ)
    (hlo : ((219) : ℝ) ≤ t) (hhi : t ≤ ((220) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate348
    (fun ht => compactCertificate348_proves ht) ((219) : ℚ) ((220) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_349 (t : ℝ)
    (hlo : ((220) : ℝ) ≤ t) (hhi : t ≤ ((221) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate349
    (fun ht => compactCertificate349_proves ht) ((220) : ℚ) ((221) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_350 (t : ℝ)
    (hlo : ((221) : ℝ) ≤ t) (hhi : t ≤ ((222) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate350
    (fun ht => compactCertificate350_proves ht) ((221) : ℚ) ((222) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_351 (t : ℝ)
    (hlo : ((222) : ℝ) ≤ t) (hhi : t ≤ ((223) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate351
    (fun ht => compactCertificate351_proves ht) ((222) : ℚ) ((223) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_352 (t : ℝ)
    (hlo : ((223) : ℝ) ≤ t) (hhi : t ≤ ((224) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate352
    (fun ht => compactCertificate352_proves ht) ((223) : ℚ) ((224) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_353 (t : ℝ)
    (hlo : ((224) : ℝ) ≤ t) (hhi : t ≤ ((225) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate353
    (fun ht => compactCertificate353_proves ht) ((224) : ℚ) ((225) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_354 (t : ℝ)
    (hlo : ((225) : ℝ) ≤ t) (hhi : t ≤ ((226) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate354
    (fun ht => compactCertificate354_proves ht) ((225) : ℚ) ((226) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_355 (t : ℝ)
    (hlo : ((226) : ℝ) ≤ t) (hhi : t ≤ ((227) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate355
    (fun ht => compactCertificate355_proves ht) ((226) : ℚ) ((227) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_356 (t : ℝ)
    (hlo : ((227) : ℝ) ≤ t) (hhi : t ≤ ((228) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate356
    (fun ht => compactCertificate356_proves ht) ((227) : ℚ) ((228) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_357 (t : ℝ)
    (hlo : ((228) : ℝ) ≤ t) (hhi : t ≤ ((229) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate357
    (fun ht => compactCertificate357_proves ht) ((228) : ℚ) ((229) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_358 (t : ℝ)
    (hlo : ((229) : ℝ) ≤ t) (hhi : t ≤ ((230) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate358
    (fun ht => compactCertificate358_proves ht) ((229) : ℚ) ((230) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_359 (t : ℝ)
    (hlo : ((230) : ℝ) ≤ t) (hhi : t ≤ ((231) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate359
    (fun ht => compactCertificate359_proves ht) ((230) : ℚ) ((231) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_360 (t : ℝ)
    (hlo : ((231) : ℝ) ≤ t) (hhi : t ≤ ((232) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate360
    (fun ht => compactCertificate360_proves ht) ((231) : ℚ) ((232) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_361 (t : ℝ)
    (hlo : ((232) : ℝ) ≤ t) (hhi : t ≤ ((233) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate361
    (fun ht => compactCertificate361_proves ht) ((232) : ℚ) ((233) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_362 (t : ℝ)
    (hlo : ((233) : ℝ) ≤ t) (hhi : t ≤ ((234) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate362
    (fun ht => compactCertificate362_proves ht) ((233) : ℚ) ((234) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_363 (t : ℝ)
    (hlo : ((234) : ℝ) ≤ t) (hhi : t ≤ ((235) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate363
    (fun ht => compactCertificate363_proves ht) ((234) : ℚ) ((235) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_364 (t : ℝ)
    (hlo : ((235) : ℝ) ≤ t) (hhi : t ≤ ((236) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate364
    (fun ht => compactCertificate364_proves ht) ((235) : ℚ) ((236) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_365 (t : ℝ)
    (hlo : ((236) : ℝ) ≤ t) (hhi : t ≤ ((237) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate365
    (fun ht => compactCertificate365_proves ht) ((236) : ℚ) ((237) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_366 (t : ℝ)
    (hlo : ((237) : ℝ) ≤ t) (hhi : t ≤ ((238) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate366
    (fun ht => compactCertificate366_proves ht) ((237) : ℚ) ((238) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_367 (t : ℝ)
    (hlo : ((238) : ℝ) ≤ t) (hhi : t ≤ ((239) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate367
    (fun ht => compactCertificate367_proves ht) ((238) : ℚ) ((239) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_368 (t : ℝ)
    (hlo : ((239) : ℝ) ≤ t) (hhi : t ≤ ((240) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate368
    (fun ht => compactCertificate368_proves ht) ((239) : ℚ) ((240) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_369 (t : ℝ)
    (hlo : ((240) : ℝ) ≤ t) (hhi : t ≤ ((241) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate369
    (fun ht => compactCertificate369_proves ht) ((240) : ℚ) ((241) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_370 (t : ℝ)
    (hlo : ((241) : ℝ) ≤ t) (hhi : t ≤ ((242) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate370
    (fun ht => compactCertificate370_proves ht) ((241) : ℚ) ((242) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_371 (t : ℝ)
    (hlo : ((242) : ℝ) ≤ t) (hhi : t ≤ ((243) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate371
    (fun ht => compactCertificate371_proves ht) ((242) : ℚ) ((243) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_372 (t : ℝ)
    (hlo : ((243) : ℝ) ≤ t) (hhi : t ≤ ((244) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate372
    (fun ht => compactCertificate372_proves ht) ((243) : ℚ) ((244) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_373 (t : ℝ)
    (hlo : ((244) : ℝ) ≤ t) (hhi : t ≤ ((245) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate373
    (fun ht => compactCertificate373_proves ht) ((244) : ℚ) ((245) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_374 (t : ℝ)
    (hlo : ((245) : ℝ) ≤ t) (hhi : t ≤ ((246) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate374
    (fun ht => compactCertificate374_proves ht) ((245) : ℚ) ((246) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_375 (t : ℝ)
    (hlo : ((246) : ℝ) ≤ t) (hhi : t ≤ ((247) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate375
    (fun ht => compactCertificate375_proves ht) ((246) : ℚ) ((247) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_376 (t : ℝ)
    (hlo : ((247) : ℝ) ≤ t) (hhi : t ≤ ((248) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate376
    (fun ht => compactCertificate376_proves ht) ((247) : ℚ) ((248) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_377 (t : ℝ)
    (hlo : ((248) : ℝ) ≤ t) (hhi : t ≤ ((249) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate377
    (fun ht => compactCertificate377_proves ht) ((248) : ℚ) ((249) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_378 (t : ℝ)
    (hlo : ((249) : ℝ) ≤ t) (hhi : t ≤ ((250) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate378
    (fun ht => compactCertificate378_proves ht) ((249) : ℚ) ((250) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_379 (t : ℝ)
    (hlo : ((250) : ℝ) ≤ t) (hhi : t ≤ ((251) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate379
    (fun ht => compactCertificate379_proves ht) ((250) : ℚ) ((251) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_380 (t : ℝ)
    (hlo : ((251) : ℝ) ≤ t) (hhi : t ≤ ((252) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate380
    (fun ht => compactCertificate380_proves ht) ((251) : ℚ) ((252) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_381 (t : ℝ)
    (hlo : ((252) : ℝ) ≤ t) (hhi : t ≤ ((253) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate381
    (fun ht => compactCertificate381_proves ht) ((252) : ℚ) ((253) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_382 (t : ℝ)
    (hlo : ((253) : ℝ) ≤ t) (hhi : t ≤ ((254) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate382
    (fun ht => compactCertificate382_proves ht) ((253) : ℚ) ((254) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_383 (t : ℝ)
    (hlo : ((254) : ℝ) ≤ t) (hhi : t ≤ ((255) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate383
    (fun ht => compactCertificate383_proves ht) ((254) : ℚ) ((255) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_384 (t : ℝ)
    (hlo : ((255) : ℝ) ≤ t) (hhi : t ≤ ((256) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate384
    (fun ht => compactCertificate384_proves ht) ((255) : ℚ) ((256) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_385 (t : ℝ)
    (hlo : ((256) : ℝ) ≤ t) (hhi : t ≤ ((257) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate385
    (fun ht => compactCertificate385_proves ht) ((256) : ℚ) ((257) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_386 (t : ℝ)
    (hlo : ((257) : ℝ) ≤ t) (hhi : t ≤ ((258) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate386
    (fun ht => compactCertificate386_proves ht) ((257) : ℚ) ((258) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_387 (t : ℝ)
    (hlo : ((258) : ℝ) ≤ t) (hhi : t ≤ ((259) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate387
    (fun ht => compactCertificate387_proves ht) ((258) : ℚ) ((259) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_388 (t : ℝ)
    (hlo : ((259) : ℝ) ≤ t) (hhi : t ≤ ((260) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate388
    (fun ht => compactCertificate388_proves ht) ((259) : ℚ) ((260) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_389 (t : ℝ)
    (hlo : ((260) : ℝ) ≤ t) (hhi : t ≤ ((261) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate389
    (fun ht => compactCertificate389_proves ht) ((260) : ℚ) ((261) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_390 (t : ℝ)
    (hlo : ((261) : ℝ) ≤ t) (hhi : t ≤ ((262) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate390
    (fun ht => compactCertificate390_proves ht) ((261) : ℚ) ((262) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_391 (t : ℝ)
    (hlo : ((262) : ℝ) ≤ t) (hhi : t ≤ ((263) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate391
    (fun ht => compactCertificate391_proves ht) ((262) : ℚ) ((263) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_392 (t : ℝ)
    (hlo : ((263) : ℝ) ≤ t) (hhi : t ≤ ((264) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate392
    (fun ht => compactCertificate392_proves ht) ((263) : ℚ) ((264) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_393 (t : ℝ)
    (hlo : ((264) : ℝ) ≤ t) (hhi : t ≤ ((265) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate393
    (fun ht => compactCertificate393_proves ht) ((264) : ℚ) ((265) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_394 (t : ℝ)
    (hlo : ((265) : ℝ) ≤ t) (hhi : t ≤ ((266) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate394
    (fun ht => compactCertificate394_proves ht) ((265) : ℚ) ((266) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_395 (t : ℝ)
    (hlo : ((266) : ℝ) ≤ t) (hhi : t ≤ ((267) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate395
    (fun ht => compactCertificate395_proves ht) ((266) : ℚ) ((267) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_396 (t : ℝ)
    (hlo : ((267) : ℝ) ≤ t) (hhi : t ≤ ((268) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate396
    (fun ht => compactCertificate396_proves ht) ((267) : ℚ) ((268) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_397 (t : ℝ)
    (hlo : ((268) : ℝ) ≤ t) (hhi : t ≤ ((269) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate397
    (fun ht => compactCertificate397_proves ht) ((268) : ℚ) ((269) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_398 (t : ℝ)
    (hlo : ((269) : ℝ) ≤ t) (hhi : t ≤ ((270) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate398
    (fun ht => compactCertificate398_proves ht) ((269) : ℚ) ((270) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_399 (t : ℝ)
    (hlo : ((270) : ℝ) ≤ t) (hhi : t ≤ ((271) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate399
    (fun ht => compactCertificate399_proves ht) ((270) : ℚ) ((271) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_400 (t : ℝ)
    (hlo : ((271) : ℝ) ≤ t) (hhi : t ≤ ((272) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate400
    (fun ht => compactCertificate400_proves ht) ((271) : ℚ) ((272) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_401 (t : ℝ)
    (hlo : ((272) : ℝ) ≤ t) (hhi : t ≤ ((273) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate401
    (fun ht => compactCertificate401_proves ht) ((272) : ℚ) ((273) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_402 (t : ℝ)
    (hlo : ((273) : ℝ) ≤ t) (hhi : t ≤ ((274) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate402
    (fun ht => compactCertificate402_proves ht) ((273) : ℚ) ((274) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_403 (t : ℝ)
    (hlo : ((274) : ℝ) ≤ t) (hhi : t ≤ ((275) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate403
    (fun ht => compactCertificate403_proves ht) ((274) : ℚ) ((275) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_404 (t : ℝ)
    (hlo : ((275) : ℝ) ≤ t) (hhi : t ≤ ((276) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate404
    (fun ht => compactCertificate404_proves ht) ((275) : ℚ) ((276) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_405 (t : ℝ)
    (hlo : ((276) : ℝ) ≤ t) (hhi : t ≤ ((277) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate405
    (fun ht => compactCertificate405_proves ht) ((276) : ℚ) ((277) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_406 (t : ℝ)
    (hlo : ((277) : ℝ) ≤ t) (hhi : t ≤ ((278) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate406
    (fun ht => compactCertificate406_proves ht) ((277) : ℚ) ((278) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_407 (t : ℝ)
    (hlo : ((278) : ℝ) ≤ t) (hhi : t ≤ ((279) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate407
    (fun ht => compactCertificate407_proves ht) ((278) : ℚ) ((279) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_408 (t : ℝ)
    (hlo : ((279) : ℝ) ≤ t) (hhi : t ≤ ((280) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate408
    (fun ht => compactCertificate408_proves ht) ((279) : ℚ) ((280) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_409 (t : ℝ)
    (hlo : ((280) : ℝ) ≤ t) (hhi : t ≤ ((281) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate409
    (fun ht => compactCertificate409_proves ht) ((280) : ℚ) ((281) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_410 (t : ℝ)
    (hlo : ((281) : ℝ) ≤ t) (hhi : t ≤ ((282) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate410
    (fun ht => compactCertificate410_proves ht) ((281) : ℚ) ((282) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_411 (t : ℝ)
    (hlo : ((282) : ℝ) ≤ t) (hhi : t ≤ ((283) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate411
    (fun ht => compactCertificate411_proves ht) ((282) : ℚ) ((283) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_412 (t : ℝ)
    (hlo : ((283) : ℝ) ≤ t) (hhi : t ≤ ((284) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate412
    (fun ht => compactCertificate412_proves ht) ((283) : ℚ) ((284) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_413 (t : ℝ)
    (hlo : ((284) : ℝ) ≤ t) (hhi : t ≤ ((285) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate413
    (fun ht => compactCertificate413_proves ht) ((284) : ℚ) ((285) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_414 (t : ℝ)
    (hlo : ((285) : ℝ) ≤ t) (hhi : t ≤ ((286) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate414
    (fun ht => compactCertificate414_proves ht) ((285) : ℚ) ((286) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_415 (t : ℝ)
    (hlo : ((286) : ℝ) ≤ t) (hhi : t ≤ ((287) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate415
    (fun ht => compactCertificate415_proves ht) ((286) : ℚ) ((287) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_416 (t : ℝ)
    (hlo : ((287) : ℝ) ≤ t) (hhi : t ≤ ((288) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate416
    (fun ht => compactCertificate416_proves ht) ((287) : ℚ) ((288) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_417 (t : ℝ)
    (hlo : ((288) : ℝ) ≤ t) (hhi : t ≤ ((289) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate417
    (fun ht => compactCertificate417_proves ht) ((288) : ℚ) ((289) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_418 (t : ℝ)
    (hlo : ((289) : ℝ) ≤ t) (hhi : t ≤ ((290) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate418
    (fun ht => compactCertificate418_proves ht) ((289) : ℚ) ((290) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_419 (t : ℝ)
    (hlo : ((290) : ℝ) ≤ t) (hhi : t ≤ ((291) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate419
    (fun ht => compactCertificate419_proves ht) ((290) : ℚ) ((291) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_420 (t : ℝ)
    (hlo : ((291) : ℝ) ≤ t) (hhi : t ≤ ((292) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate420
    (fun ht => compactCertificate420_proves ht) ((291) : ℚ) ((292) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_421 (t : ℝ)
    (hlo : ((292) : ℝ) ≤ t) (hhi : t ≤ ((293) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate421
    (fun ht => compactCertificate421_proves ht) ((292) : ℚ) ((293) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_422 (t : ℝ)
    (hlo : ((293) : ℝ) ≤ t) (hhi : t ≤ ((294) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate422
    (fun ht => compactCertificate422_proves ht) ((293) : ℚ) ((294) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_423 (t : ℝ)
    (hlo : ((294) : ℝ) ≤ t) (hhi : t ≤ ((295) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate423
    (fun ht => compactCertificate423_proves ht) ((294) : ℚ) ((295) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_424 (t : ℝ)
    (hlo : ((295) : ℝ) ≤ t) (hhi : t ≤ ((296) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate424
    (fun ht => compactCertificate424_proves ht) ((295) : ℚ) ((296) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_425 (t : ℝ)
    (hlo : ((296) : ℝ) ≤ t) (hhi : t ≤ ((297) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate425
    (fun ht => compactCertificate425_proves ht) ((296) : ℚ) ((297) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_426 (t : ℝ)
    (hlo : ((297) : ℝ) ≤ t) (hhi : t ≤ ((298) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate426
    (fun ht => compactCertificate426_proves ht) ((297) : ℚ) ((298) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_427 (t : ℝ)
    (hlo : ((298) : ℝ) ≤ t) (hhi : t ≤ ((299) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate427
    (fun ht => compactCertificate427_proves ht) ((298) : ℚ) ((299) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_428 (t : ℝ)
    (hlo : ((299) : ℝ) ≤ t) (hhi : t ≤ ((300) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate428
    (fun ht => compactCertificate428_proves ht) ((299) : ℚ) ((300) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_429 (t : ℝ)
    (hlo : ((300) : ℝ) ≤ t) (hhi : t ≤ ((301) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate429
    (fun ht => compactCertificate429_proves ht) ((300) : ℚ) ((301) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_430 (t : ℝ)
    (hlo : ((301) : ℝ) ≤ t) (hhi : t ≤ ((302) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate430
    (fun ht => compactCertificate430_proves ht) ((301) : ℚ) ((302) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_431 (t : ℝ)
    (hlo : ((302) : ℝ) ≤ t) (hhi : t ≤ ((303) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate431
    (fun ht => compactCertificate431_proves ht) ((302) : ℚ) ((303) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_432 (t : ℝ)
    (hlo : ((303) : ℝ) ≤ t) (hhi : t ≤ ((304) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate432
    (fun ht => compactCertificate432_proves ht) ((303) : ℚ) ((304) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_433 (t : ℝ)
    (hlo : ((304) : ℝ) ≤ t) (hhi : t ≤ ((305) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate433
    (fun ht => compactCertificate433_proves ht) ((304) : ℚ) ((305) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_434 (t : ℝ)
    (hlo : ((305) : ℝ) ≤ t) (hhi : t ≤ ((306) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate434
    (fun ht => compactCertificate434_proves ht) ((305) : ℚ) ((306) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_435 (t : ℝ)
    (hlo : ((306) : ℝ) ≤ t) (hhi : t ≤ ((307) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate435
    (fun ht => compactCertificate435_proves ht) ((306) : ℚ) ((307) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_436 (t : ℝ)
    (hlo : ((307) : ℝ) ≤ t) (hhi : t ≤ ((308) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate436
    (fun ht => compactCertificate436_proves ht) ((307) : ℚ) ((308) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_437 (t : ℝ)
    (hlo : ((308) : ℝ) ≤ t) (hhi : t ≤ ((309) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate437
    (fun ht => compactCertificate437_proves ht) ((308) : ℚ) ((309) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_438 (t : ℝ)
    (hlo : ((309) : ℝ) ≤ t) (hhi : t ≤ ((310) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate438
    (fun ht => compactCertificate438_proves ht) ((309) : ℚ) ((310) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_439 (t : ℝ)
    (hlo : ((310) : ℝ) ≤ t) (hhi : t ≤ ((311) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate439
    (fun ht => compactCertificate439_proves ht) ((310) : ℚ) ((311) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_440 (t : ℝ)
    (hlo : ((311) : ℝ) ≤ t) (hhi : t ≤ ((312) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate440
    (fun ht => compactCertificate440_proves ht) ((311) : ℚ) ((312) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_441 (t : ℝ)
    (hlo : ((312) : ℝ) ≤ t) (hhi : t ≤ ((313) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate441
    (fun ht => compactCertificate441_proves ht) ((312) : ℚ) ((313) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_442 (t : ℝ)
    (hlo : ((313) : ℝ) ≤ t) (hhi : t ≤ ((314) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate442
    (fun ht => compactCertificate442_proves ht) ((313) : ℚ) ((314) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_443 (t : ℝ)
    (hlo : ((314) : ℝ) ≤ t) (hhi : t ≤ ((315) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate443
    (fun ht => compactCertificate443_proves ht) ((314) : ℚ) ((315) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_444 (t : ℝ)
    (hlo : ((315) : ℝ) ≤ t) (hhi : t ≤ ((316) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate444
    (fun ht => compactCertificate444_proves ht) ((315) : ℚ) ((316) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_445 (t : ℝ)
    (hlo : ((316) : ℝ) ≤ t) (hhi : t ≤ ((317) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate445
    (fun ht => compactCertificate445_proves ht) ((316) : ℚ) ((317) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_446 (t : ℝ)
    (hlo : ((317) : ℝ) ≤ t) (hhi : t ≤ ((318) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate446
    (fun ht => compactCertificate446_proves ht) ((317) : ℚ) ((318) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_447 (t : ℝ)
    (hlo : ((318) : ℝ) ≤ t) (hhi : t ≤ ((319) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate447
    (fun ht => compactCertificate447_proves ht) ((318) : ℚ) ((319) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_448 (t : ℝ)
    (hlo : ((319) : ℝ) ≤ t) (hhi : t ≤ ((320) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate448
    (fun ht => compactCertificate448_proves ht) ((319) : ℚ) ((320) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_449 (t : ℝ)
    (hlo : ((320) : ℝ) ≤ t) (hhi : t ≤ ((321) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate449
    (fun ht => compactCertificate449_proves ht) ((320) : ℚ) ((321) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_450 (t : ℝ)
    (hlo : ((321) : ℝ) ≤ t) (hhi : t ≤ ((322) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate450
    (fun ht => compactCertificate450_proves ht) ((321) : ℚ) ((322) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_451 (t : ℝ)
    (hlo : ((322) : ℝ) ≤ t) (hhi : t ≤ ((323) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate451
    (fun ht => compactCertificate451_proves ht) ((322) : ℚ) ((323) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_452 (t : ℝ)
    (hlo : ((323) : ℝ) ≤ t) (hhi : t ≤ ((324) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate452
    (fun ht => compactCertificate452_proves ht) ((323) : ℚ) ((324) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_453 (t : ℝ)
    (hlo : ((324) : ℝ) ≤ t) (hhi : t ≤ ((325) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate453
    (fun ht => compactCertificate453_proves ht) ((324) : ℚ) ((325) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_454 (t : ℝ)
    (hlo : ((325) : ℝ) ≤ t) (hhi : t ≤ ((326) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate454
    (fun ht => compactCertificate454_proves ht) ((325) : ℚ) ((326) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_455 (t : ℝ)
    (hlo : ((326) : ℝ) ≤ t) (hhi : t ≤ ((327) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate455
    (fun ht => compactCertificate455_proves ht) ((326) : ℚ) ((327) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_456 (t : ℝ)
    (hlo : ((327) : ℝ) ≤ t) (hhi : t ≤ ((328) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate456
    (fun ht => compactCertificate456_proves ht) ((327) : ℚ) ((328) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_457 (t : ℝ)
    (hlo : ((328) : ℝ) ≤ t) (hhi : t ≤ ((329) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate457
    (fun ht => compactCertificate457_proves ht) ((328) : ℚ) ((329) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_458 (t : ℝ)
    (hlo : ((329) : ℝ) ≤ t) (hhi : t ≤ ((330) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate458
    (fun ht => compactCertificate458_proves ht) ((329) : ℚ) ((330) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_459 (t : ℝ)
    (hlo : ((330) : ℝ) ≤ t) (hhi : t ≤ ((331) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate459
    (fun ht => compactCertificate459_proves ht) ((330) : ℚ) ((331) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_460 (t : ℝ)
    (hlo : ((331) : ℝ) ≤ t) (hhi : t ≤ ((332) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate460
    (fun ht => compactCertificate460_proves ht) ((331) : ℚ) ((332) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_461 (t : ℝ)
    (hlo : ((332) : ℝ) ≤ t) (hhi : t ≤ ((333) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate461
    (fun ht => compactCertificate461_proves ht) ((332) : ℚ) ((333) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_462 (t : ℝ)
    (hlo : ((333) : ℝ) ≤ t) (hhi : t ≤ ((334) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate462
    (fun ht => compactCertificate462_proves ht) ((333) : ℚ) ((334) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_463 (t : ℝ)
    (hlo : ((334) : ℝ) ≤ t) (hhi : t ≤ ((335) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate463
    (fun ht => compactCertificate463_proves ht) ((334) : ℚ) ((335) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_464 (t : ℝ)
    (hlo : ((335) : ℝ) ≤ t) (hhi : t ≤ ((336) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate464
    (fun ht => compactCertificate464_proves ht) ((335) : ℚ) ((336) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_465 (t : ℝ)
    (hlo : ((336) : ℝ) ≤ t) (hhi : t ≤ ((337) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate465
    (fun ht => compactCertificate465_proves ht) ((336) : ℚ) ((337) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_466 (t : ℝ)
    (hlo : ((337) : ℝ) ≤ t) (hhi : t ≤ ((338) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate466
    (fun ht => compactCertificate466_proves ht) ((337) : ℚ) ((338) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_467 (t : ℝ)
    (hlo : ((338) : ℝ) ≤ t) (hhi : t ≤ ((339) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate467
    (fun ht => compactCertificate467_proves ht) ((338) : ℚ) ((339) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_468 (t : ℝ)
    (hlo : ((339) : ℝ) ≤ t) (hhi : t ≤ ((340) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate468
    (fun ht => compactCertificate468_proves ht) ((339) : ℚ) ((340) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_469 (t : ℝ)
    (hlo : ((340) : ℝ) ≤ t) (hhi : t ≤ ((341) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate469
    (fun ht => compactCertificate469_proves ht) ((340) : ℚ) ((341) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_470 (t : ℝ)
    (hlo : ((341) : ℝ) ≤ t) (hhi : t ≤ ((342) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate470
    (fun ht => compactCertificate470_proves ht) ((341) : ℚ) ((342) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_471 (t : ℝ)
    (hlo : ((342) : ℝ) ≤ t) (hhi : t ≤ ((343) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate471
    (fun ht => compactCertificate471_proves ht) ((342) : ℚ) ((343) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_472 (t : ℝ)
    (hlo : ((343) : ℝ) ≤ t) (hhi : t ≤ ((344) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate472
    (fun ht => compactCertificate472_proves ht) ((343) : ℚ) ((344) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_473 (t : ℝ)
    (hlo : ((344) : ℝ) ≤ t) (hhi : t ≤ ((345) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate473
    (fun ht => compactCertificate473_proves ht) ((344) : ℚ) ((345) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_474 (t : ℝ)
    (hlo : ((345) : ℝ) ≤ t) (hhi : t ≤ ((346) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate474
    (fun ht => compactCertificate474_proves ht) ((345) : ℚ) ((346) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_475 (t : ℝ)
    (hlo : ((346) : ℝ) ≤ t) (hhi : t ≤ ((347) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate475
    (fun ht => compactCertificate475_proves ht) ((346) : ℚ) ((347) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_476 (t : ℝ)
    (hlo : ((347) : ℝ) ≤ t) (hhi : t ≤ ((348) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate476
    (fun ht => compactCertificate476_proves ht) ((347) : ℚ) ((348) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_477 (t : ℝ)
    (hlo : ((348) : ℝ) ≤ t) (hhi : t ≤ ((349) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate477
    (fun ht => compactCertificate477_proves ht) ((348) : ℚ) ((349) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_478 (t : ℝ)
    (hlo : ((349) : ℝ) ≤ t) (hhi : t ≤ ((350) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate478
    (fun ht => compactCertificate478_proves ht) ((349) : ℚ) ((350) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_479 (t : ℝ)
    (hlo : ((350) : ℝ) ≤ t) (hhi : t ≤ ((351) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate479
    (fun ht => compactCertificate479_proves ht) ((350) : ℚ) ((351) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_480 (t : ℝ)
    (hlo : ((351) : ℝ) ≤ t) (hhi : t ≤ ((352) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate480
    (fun ht => compactCertificate480_proves ht) ((351) : ℚ) ((352) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_481 (t : ℝ)
    (hlo : ((352) : ℝ) ≤ t) (hhi : t ≤ ((353) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate481
    (fun ht => compactCertificate481_proves ht) ((352) : ℚ) ((353) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_482 (t : ℝ)
    (hlo : ((353) : ℝ) ≤ t) (hhi : t ≤ ((354) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate482
    (fun ht => compactCertificate482_proves ht) ((353) : ℚ) ((354) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_483 (t : ℝ)
    (hlo : ((354) : ℝ) ≤ t) (hhi : t ≤ ((355) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate483
    (fun ht => compactCertificate483_proves ht) ((354) : ℚ) ((355) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_484 (t : ℝ)
    (hlo : ((355) : ℝ) ≤ t) (hhi : t ≤ ((356) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate484
    (fun ht => compactCertificate484_proves ht) ((355) : ℚ) ((356) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_485 (t : ℝ)
    (hlo : ((356) : ℝ) ≤ t) (hhi : t ≤ ((357) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate485
    (fun ht => compactCertificate485_proves ht) ((356) : ℚ) ((357) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_486 (t : ℝ)
    (hlo : ((357) : ℝ) ≤ t) (hhi : t ≤ ((358) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate486
    (fun ht => compactCertificate486_proves ht) ((357) : ℚ) ((358) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_487 (t : ℝ)
    (hlo : ((358) : ℝ) ≤ t) (hhi : t ≤ ((359) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate487
    (fun ht => compactCertificate487_proves ht) ((358) : ℚ) ((359) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_488 (t : ℝ)
    (hlo : ((359) : ℝ) ≤ t) (hhi : t ≤ ((360) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate488
    (fun ht => compactCertificate488_proves ht) ((359) : ℚ) ((360) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_489 (t : ℝ)
    (hlo : ((360) : ℝ) ≤ t) (hhi : t ≤ ((361) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate489
    (fun ht => compactCertificate489_proves ht) ((360) : ℚ) ((361) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_490 (t : ℝ)
    (hlo : ((361) : ℝ) ≤ t) (hhi : t ≤ ((362) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate490
    (fun ht => compactCertificate490_proves ht) ((361) : ℚ) ((362) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_491 (t : ℝ)
    (hlo : ((362) : ℝ) ≤ t) (hhi : t ≤ ((363) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate491
    (fun ht => compactCertificate491_proves ht) ((362) : ℚ) ((363) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_492 (t : ℝ)
    (hlo : ((363) : ℝ) ≤ t) (hhi : t ≤ ((364) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate492
    (fun ht => compactCertificate492_proves ht) ((363) : ℚ) ((364) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_493 (t : ℝ)
    (hlo : ((364) : ℝ) ≤ t) (hhi : t ≤ ((365) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate493
    (fun ht => compactCertificate493_proves ht) ((364) : ℚ) ((365) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_494 (t : ℝ)
    (hlo : ((365) : ℝ) ≤ t) (hhi : t ≤ ((366) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate494
    (fun ht => compactCertificate494_proves ht) ((365) : ℚ) ((366) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_495 (t : ℝ)
    (hlo : ((366) : ℝ) ≤ t) (hhi : t ≤ ((367) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate495
    (fun ht => compactCertificate495_proves ht) ((366) : ℚ) ((367) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_496 (t : ℝ)
    (hlo : ((367) : ℝ) ≤ t) (hhi : t ≤ ((368) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate496
    (fun ht => compactCertificate496_proves ht) ((367) : ℚ) ((368) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_497 (t : ℝ)
    (hlo : ((368) : ℝ) ≤ t) (hhi : t ≤ ((369) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate497
    (fun ht => compactCertificate497_proves ht) ((368) : ℚ) ((369) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_498 (t : ℝ)
    (hlo : ((369) : ℝ) ≤ t) (hhi : t ≤ ((370) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate498
    (fun ht => compactCertificate498_proves ht) ((369) : ℚ) ((370) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_499 (t : ℝ)
    (hlo : ((370) : ℝ) ≤ t) (hhi : t ≤ ((371) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate499
    (fun ht => compactCertificate499_proves ht) ((370) : ℚ) ((371) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_500 (t : ℝ)
    (hlo : ((371) : ℝ) ≤ t) (hhi : t ≤ ((372) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate500
    (fun ht => compactCertificate500_proves ht) ((371) : ℚ) ((372) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_501 (t : ℝ)
    (hlo : ((372) : ℝ) ≤ t) (hhi : t ≤ ((373) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate501
    (fun ht => compactCertificate501_proves ht) ((372) : ℚ) ((373) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_502 (t : ℝ)
    (hlo : ((373) : ℝ) ≤ t) (hhi : t ≤ ((374) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate502
    (fun ht => compactCertificate502_proves ht) ((373) : ℚ) ((374) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_503 (t : ℝ)
    (hlo : ((374) : ℝ) ≤ t) (hhi : t ≤ ((375) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate503
    (fun ht => compactCertificate503_proves ht) ((374) : ℚ) ((375) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_504 (t : ℝ)
    (hlo : ((375) : ℝ) ≤ t) (hhi : t ≤ ((376) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate504
    (fun ht => compactCertificate504_proves ht) ((375) : ℚ) ((376) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_505 (t : ℝ)
    (hlo : ((376) : ℝ) ≤ t) (hhi : t ≤ ((377) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate505
    (fun ht => compactCertificate505_proves ht) ((376) : ℚ) ((377) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_506 (t : ℝ)
    (hlo : ((377) : ℝ) ≤ t) (hhi : t ≤ ((378) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate506
    (fun ht => compactCertificate506_proves ht) ((377) : ℚ) ((378) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_507 (t : ℝ)
    (hlo : ((378) : ℝ) ≤ t) (hhi : t ≤ ((379) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate507
    (fun ht => compactCertificate507_proves ht) ((378) : ℚ) ((379) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_508 (t : ℝ)
    (hlo : ((379) : ℝ) ≤ t) (hhi : t ≤ ((380) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate508
    (fun ht => compactCertificate508_proves ht) ((379) : ℚ) ((380) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_509 (t : ℝ)
    (hlo : ((380) : ℝ) ≤ t) (hhi : t ≤ ((381) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate509
    (fun ht => compactCertificate509_proves ht) ((380) : ℚ) ((381) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_510 (t : ℝ)
    (hlo : ((381) : ℝ) ≤ t) (hhi : t ≤ ((382) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate510
    (fun ht => compactCertificate510_proves ht) ((381) : ℚ) ((382) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_511 (t : ℝ)
    (hlo : ((382) : ℝ) ≤ t) (hhi : t ≤ ((383) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate511
    (fun ht => compactCertificate511_proves ht) ((382) : ℚ) ((383) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_512 (t : ℝ)
    (hlo : ((383) : ℝ) ≤ t) (hhi : t ≤ ((384) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate512
    (fun ht => compactCertificate512_proves ht) ((383) : ℚ) ((384) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_513 (t : ℝ)
    (hlo : ((384) : ℝ) ≤ t) (hhi : t ≤ ((385) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate513
    (fun ht => compactCertificate513_proves ht) ((384) : ℚ) ((385) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_514 (t : ℝ)
    (hlo : ((385) : ℝ) ≤ t) (hhi : t ≤ ((386) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate514
    (fun ht => compactCertificate514_proves ht) ((385) : ℚ) ((386) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_515 (t : ℝ)
    (hlo : ((386) : ℝ) ≤ t) (hhi : t ≤ ((387) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate515
    (fun ht => compactCertificate515_proves ht) ((386) : ℚ) ((387) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_516 (t : ℝ)
    (hlo : ((387) : ℝ) ≤ t) (hhi : t ≤ ((388) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate516
    (fun ht => compactCertificate516_proves ht) ((387) : ℚ) ((388) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_517 (t : ℝ)
    (hlo : ((388) : ℝ) ≤ t) (hhi : t ≤ ((389) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate517
    (fun ht => compactCertificate517_proves ht) ((388) : ℚ) ((389) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_518 (t : ℝ)
    (hlo : ((389) : ℝ) ≤ t) (hhi : t ≤ ((390) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate518
    (fun ht => compactCertificate518_proves ht) ((389) : ℚ) ((390) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_519 (t : ℝ)
    (hlo : ((390) : ℝ) ≤ t) (hhi : t ≤ ((391) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate519
    (fun ht => compactCertificate519_proves ht) ((390) : ℚ) ((391) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_520 (t : ℝ)
    (hlo : ((391) : ℝ) ≤ t) (hhi : t ≤ ((392) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate520
    (fun ht => compactCertificate520_proves ht) ((391) : ℚ) ((392) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_521 (t : ℝ)
    (hlo : ((392) : ℝ) ≤ t) (hhi : t ≤ ((393) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate521
    (fun ht => compactCertificate521_proves ht) ((392) : ℚ) ((393) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_522 (t : ℝ)
    (hlo : ((393) : ℝ) ≤ t) (hhi : t ≤ ((394) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate522
    (fun ht => compactCertificate522_proves ht) ((393) : ℚ) ((394) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_523 (t : ℝ)
    (hlo : ((394) : ℝ) ≤ t) (hhi : t ≤ ((395) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate523
    (fun ht => compactCertificate523_proves ht) ((394) : ℚ) ((395) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_524 (t : ℝ)
    (hlo : ((395) : ℝ) ≤ t) (hhi : t ≤ ((396) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate524
    (fun ht => compactCertificate524_proves ht) ((395) : ℚ) ((396) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_525 (t : ℝ)
    (hlo : ((396) : ℝ) ≤ t) (hhi : t ≤ ((397) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate525
    (fun ht => compactCertificate525_proves ht) ((396) : ℚ) ((397) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_526 (t : ℝ)
    (hlo : ((397) : ℝ) ≤ t) (hhi : t ≤ ((398) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate526
    (fun ht => compactCertificate526_proves ht) ((397) : ℚ) ((398) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_527 (t : ℝ)
    (hlo : ((398) : ℝ) ≤ t) (hhi : t ≤ ((399) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate527
    (fun ht => compactCertificate527_proves ht) ((398) : ℚ) ((399) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_528 (t : ℝ)
    (hlo : ((399) : ℝ) ≤ t) (hhi : t ≤ ((400) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate528
    (fun ht => compactCertificate528_proves ht) ((399) : ℚ) ((400) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_529 (t : ℝ)
    (hlo : ((400) : ℝ) ≤ t) (hhi : t ≤ ((401) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate529
    (fun ht => compactCertificate529_proves ht) ((400) : ℚ) ((401) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_530 (t : ℝ)
    (hlo : ((401) : ℝ) ≤ t) (hhi : t ≤ ((402) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate530
    (fun ht => compactCertificate530_proves ht) ((401) : ℚ) ((402) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_531 (t : ℝ)
    (hlo : ((402) : ℝ) ≤ t) (hhi : t ≤ ((403) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate531
    (fun ht => compactCertificate531_proves ht) ((402) : ℚ) ((403) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_532 (t : ℝ)
    (hlo : ((403) : ℝ) ≤ t) (hhi : t ≤ ((404) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate532
    (fun ht => compactCertificate532_proves ht) ((403) : ℚ) ((404) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_533 (t : ℝ)
    (hlo : ((404) : ℝ) ≤ t) (hhi : t ≤ ((405) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate533
    (fun ht => compactCertificate533_proves ht) ((404) : ℚ) ((405) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_534 (t : ℝ)
    (hlo : ((405) : ℝ) ≤ t) (hhi : t ≤ ((406) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate534
    (fun ht => compactCertificate534_proves ht) ((405) : ℚ) ((406) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_535 (t : ℝ)
    (hlo : ((406) : ℝ) ≤ t) (hhi : t ≤ ((407) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate535
    (fun ht => compactCertificate535_proves ht) ((406) : ℚ) ((407) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_536 (t : ℝ)
    (hlo : ((407) : ℝ) ≤ t) (hhi : t ≤ ((408) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate536
    (fun ht => compactCertificate536_proves ht) ((407) : ℚ) ((408) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_537 (t : ℝ)
    (hlo : ((408) : ℝ) ≤ t) (hhi : t ≤ ((409) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate537
    (fun ht => compactCertificate537_proves ht) ((408) : ℚ) ((409) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_538 (t : ℝ)
    (hlo : ((409) : ℝ) ≤ t) (hhi : t ≤ ((410) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate538
    (fun ht => compactCertificate538_proves ht) ((409) : ℚ) ((410) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_539 (t : ℝ)
    (hlo : ((410) : ℝ) ≤ t) (hhi : t ≤ ((411) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate539
    (fun ht => compactCertificate539_proves ht) ((410) : ℚ) ((411) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_540 (t : ℝ)
    (hlo : ((411) : ℝ) ≤ t) (hhi : t ≤ ((412) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate540
    (fun ht => compactCertificate540_proves ht) ((411) : ℚ) ((412) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_541 (t : ℝ)
    (hlo : ((412) : ℝ) ≤ t) (hhi : t ≤ ((413) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate541
    (fun ht => compactCertificate541_proves ht) ((412) : ℚ) ((413) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_542 (t : ℝ)
    (hlo : ((413) : ℝ) ≤ t) (hhi : t ≤ ((414) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate542
    (fun ht => compactCertificate542_proves ht) ((413) : ℚ) ((414) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_543 (t : ℝ)
    (hlo : ((414) : ℝ) ≤ t) (hhi : t ≤ ((415) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate543
    (fun ht => compactCertificate543_proves ht) ((414) : ℚ) ((415) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_544 (t : ℝ)
    (hlo : ((415) : ℝ) ≤ t) (hhi : t ≤ ((416) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate544
    (fun ht => compactCertificate544_proves ht) ((415) : ℚ) ((416) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_545 (t : ℝ)
    (hlo : ((416) : ℝ) ≤ t) (hhi : t ≤ ((417) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate545
    (fun ht => compactCertificate545_proves ht) ((416) : ℚ) ((417) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_546 (t : ℝ)
    (hlo : ((417) : ℝ) ≤ t) (hhi : t ≤ ((418) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate546
    (fun ht => compactCertificate546_proves ht) ((417) : ℚ) ((418) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_547 (t : ℝ)
    (hlo : ((418) : ℝ) ≤ t) (hhi : t ≤ ((419) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate547
    (fun ht => compactCertificate547_proves ht) ((418) : ℚ) ((419) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_548 (t : ℝ)
    (hlo : ((419) : ℝ) ≤ t) (hhi : t ≤ ((420) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate548
    (fun ht => compactCertificate548_proves ht) ((419) : ℚ) ((420) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_549 (t : ℝ)
    (hlo : ((420) : ℝ) ≤ t) (hhi : t ≤ ((421) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate549
    (fun ht => compactCertificate549_proves ht) ((420) : ℚ) ((421) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_550 (t : ℝ)
    (hlo : ((421) : ℝ) ≤ t) (hhi : t ≤ ((422) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate550
    (fun ht => compactCertificate550_proves ht) ((421) : ℚ) ((422) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_551 (t : ℝ)
    (hlo : ((422) : ℝ) ≤ t) (hhi : t ≤ ((423) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate551
    (fun ht => compactCertificate551_proves ht) ((422) : ℚ) ((423) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_552 (t : ℝ)
    (hlo : ((423) : ℝ) ≤ t) (hhi : t ≤ ((424) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate552
    (fun ht => compactCertificate552_proves ht) ((423) : ℚ) ((424) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_553 (t : ℝ)
    (hlo : ((424) : ℝ) ≤ t) (hhi : t ≤ ((425) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate553
    (fun ht => compactCertificate553_proves ht) ((424) : ℚ) ((425) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_554 (t : ℝ)
    (hlo : ((425) : ℝ) ≤ t) (hhi : t ≤ ((426) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate554
    (fun ht => compactCertificate554_proves ht) ((425) : ℚ) ((426) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_555 (t : ℝ)
    (hlo : ((426) : ℝ) ≤ t) (hhi : t ≤ ((427) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate555
    (fun ht => compactCertificate555_proves ht) ((426) : ℚ) ((427) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_556 (t : ℝ)
    (hlo : ((427) : ℝ) ≤ t) (hhi : t ≤ ((428) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate556
    (fun ht => compactCertificate556_proves ht) ((427) : ℚ) ((428) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_557 (t : ℝ)
    (hlo : ((428) : ℝ) ≤ t) (hhi : t ≤ ((429) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate557
    (fun ht => compactCertificate557_proves ht) ((428) : ℚ) ((429) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_558 (t : ℝ)
    (hlo : ((429) : ℝ) ≤ t) (hhi : t ≤ ((430) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate558
    (fun ht => compactCertificate558_proves ht) ((429) : ℚ) ((430) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_559 (t : ℝ)
    (hlo : ((430) : ℝ) ≤ t) (hhi : t ≤ ((431) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate559
    (fun ht => compactCertificate559_proves ht) ((430) : ℚ) ((431) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_560 (t : ℝ)
    (hlo : ((431) : ℝ) ≤ t) (hhi : t ≤ ((432) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate560
    (fun ht => compactCertificate560_proves ht) ((431) : ℚ) ((432) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_561 (t : ℝ)
    (hlo : ((432) : ℝ) ≤ t) (hhi : t ≤ ((433) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate561
    (fun ht => compactCertificate561_proves ht) ((432) : ℚ) ((433) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_562 (t : ℝ)
    (hlo : ((433) : ℝ) ≤ t) (hhi : t ≤ ((434) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate562
    (fun ht => compactCertificate562_proves ht) ((433) : ℚ) ((434) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_563 (t : ℝ)
    (hlo : ((434) : ℝ) ≤ t) (hhi : t ≤ ((435) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate563
    (fun ht => compactCertificate563_proves ht) ((434) : ℚ) ((435) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_564 (t : ℝ)
    (hlo : ((435) : ℝ) ≤ t) (hhi : t ≤ ((436) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate564
    (fun ht => compactCertificate564_proves ht) ((435) : ℚ) ((436) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_565 (t : ℝ)
    (hlo : ((436) : ℝ) ≤ t) (hhi : t ≤ ((437) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate565
    (fun ht => compactCertificate565_proves ht) ((436) : ℚ) ((437) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_566 (t : ℝ)
    (hlo : ((437) : ℝ) ≤ t) (hhi : t ≤ ((438) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate566
    (fun ht => compactCertificate566_proves ht) ((437) : ℚ) ((438) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_567 (t : ℝ)
    (hlo : ((438) : ℝ) ≤ t) (hhi : t ≤ ((439) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate567
    (fun ht => compactCertificate567_proves ht) ((438) : ℚ) ((439) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_568 (t : ℝ)
    (hlo : ((439) : ℝ) ≤ t) (hhi : t ≤ ((440) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate568
    (fun ht => compactCertificate568_proves ht) ((439) : ℚ) ((440) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_569 (t : ℝ)
    (hlo : ((440) : ℝ) ≤ t) (hhi : t ≤ ((441) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate569
    (fun ht => compactCertificate569_proves ht) ((440) : ℚ) ((441) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_570 (t : ℝ)
    (hlo : ((441) : ℝ) ≤ t) (hhi : t ≤ ((442) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate570
    (fun ht => compactCertificate570_proves ht) ((441) : ℚ) ((442) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_571 (t : ℝ)
    (hlo : ((442) : ℝ) ≤ t) (hhi : t ≤ ((443) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate571
    (fun ht => compactCertificate571_proves ht) ((442) : ℚ) ((443) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_572 (t : ℝ)
    (hlo : ((443) : ℝ) ≤ t) (hhi : t ≤ ((444) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate572
    (fun ht => compactCertificate572_proves ht) ((443) : ℚ) ((444) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_573 (t : ℝ)
    (hlo : ((444) : ℝ) ≤ t) (hhi : t ≤ ((445) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate573
    (fun ht => compactCertificate573_proves ht) ((444) : ℚ) ((445) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_574 (t : ℝ)
    (hlo : ((445) : ℝ) ≤ t) (hhi : t ≤ ((446) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate574
    (fun ht => compactCertificate574_proves ht) ((445) : ℚ) ((446) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_575 (t : ℝ)
    (hlo : ((446) : ℝ) ≤ t) (hhi : t ≤ ((447) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate575
    (fun ht => compactCertificate575_proves ht) ((446) : ℚ) ((447) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_576 (t : ℝ)
    (hlo : ((447) : ℝ) ≤ t) (hhi : t ≤ ((448) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate576
    (fun ht => compactCertificate576_proves ht) ((447) : ℚ) ((448) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_577 (t : ℝ)
    (hlo : ((448) : ℝ) ≤ t) (hhi : t ≤ ((449) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate577
    (fun ht => compactCertificate577_proves ht) ((448) : ℚ) ((449) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_578 (t : ℝ)
    (hlo : ((449) : ℝ) ≤ t) (hhi : t ≤ ((450) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate578
    (fun ht => compactCertificate578_proves ht) ((449) : ℚ) ((450) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_579 (t : ℝ)
    (hlo : ((450) : ℝ) ≤ t) (hhi : t ≤ ((451) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate579
    (fun ht => compactCertificate579_proves ht) ((450) : ℚ) ((451) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_580 (t : ℝ)
    (hlo : ((451) : ℝ) ≤ t) (hhi : t ≤ ((452) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate580
    (fun ht => compactCertificate580_proves ht) ((451) : ℚ) ((452) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_581 (t : ℝ)
    (hlo : ((452) : ℝ) ≤ t) (hhi : t ≤ ((453) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate581
    (fun ht => compactCertificate581_proves ht) ((452) : ℚ) ((453) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_582 (t : ℝ)
    (hlo : ((453) : ℝ) ≤ t) (hhi : t ≤ ((454) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate582
    (fun ht => compactCertificate582_proves ht) ((453) : ℚ) ((454) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_583 (t : ℝ)
    (hlo : ((454) : ℝ) ≤ t) (hhi : t ≤ ((455) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate583
    (fun ht => compactCertificate583_proves ht) ((454) : ℚ) ((455) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_584 (t : ℝ)
    (hlo : ((455) : ℝ) ≤ t) (hhi : t ≤ ((456) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate584
    (fun ht => compactCertificate584_proves ht) ((455) : ℚ) ((456) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_585 (t : ℝ)
    (hlo : ((456) : ℝ) ≤ t) (hhi : t ≤ ((457) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate585
    (fun ht => compactCertificate585_proves ht) ((456) : ℚ) ((457) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_586 (t : ℝ)
    (hlo : ((457) : ℝ) ≤ t) (hhi : t ≤ ((458) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate586
    (fun ht => compactCertificate586_proves ht) ((457) : ℚ) ((458) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_587 (t : ℝ)
    (hlo : ((458) : ℝ) ≤ t) (hhi : t ≤ ((459) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate587
    (fun ht => compactCertificate587_proves ht) ((458) : ℚ) ((459) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_588 (t : ℝ)
    (hlo : ((459) : ℝ) ≤ t) (hhi : t ≤ ((460) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate588
    (fun ht => compactCertificate588_proves ht) ((459) : ℚ) ((460) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_589 (t : ℝ)
    (hlo : ((460) : ℝ) ≤ t) (hhi : t ≤ ((461) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate589
    (fun ht => compactCertificate589_proves ht) ((460) : ℚ) ((461) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_590 (t : ℝ)
    (hlo : ((461) : ℝ) ≤ t) (hhi : t ≤ ((462) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate590
    (fun ht => compactCertificate590_proves ht) ((461) : ℚ) ((462) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_591 (t : ℝ)
    (hlo : ((462) : ℝ) ≤ t) (hhi : t ≤ ((463) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate591
    (fun ht => compactCertificate591_proves ht) ((462) : ℚ) ((463) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_592 (t : ℝ)
    (hlo : ((463) : ℝ) ≤ t) (hhi : t ≤ ((464) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate592
    (fun ht => compactCertificate592_proves ht) ((463) : ℚ) ((464) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_593 (t : ℝ)
    (hlo : ((464) : ℝ) ≤ t) (hhi : t ≤ ((465) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate593
    (fun ht => compactCertificate593_proves ht) ((464) : ℚ) ((465) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_594 (t : ℝ)
    (hlo : ((465) : ℝ) ≤ t) (hhi : t ≤ ((466) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate594
    (fun ht => compactCertificate594_proves ht) ((465) : ℚ) ((466) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_595 (t : ℝ)
    (hlo : ((466) : ℝ) ≤ t) (hhi : t ≤ ((467) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate595
    (fun ht => compactCertificate595_proves ht) ((466) : ℚ) ((467) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_596 (t : ℝ)
    (hlo : ((467) : ℝ) ≤ t) (hhi : t ≤ ((468) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate596
    (fun ht => compactCertificate596_proves ht) ((467) : ℚ) ((468) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_597 (t : ℝ)
    (hlo : ((468) : ℝ) ≤ t) (hhi : t ≤ ((469) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate597
    (fun ht => compactCertificate597_proves ht) ((468) : ℚ) ((469) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_598 (t : ℝ)
    (hlo : ((469) : ℝ) ≤ t) (hhi : t ≤ ((470) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate598
    (fun ht => compactCertificate598_proves ht) ((469) : ℚ) ((470) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_599 (t : ℝ)
    (hlo : ((470) : ℝ) ≤ t) (hhi : t ≤ ((471) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate599
    (fun ht => compactCertificate599_proves ht) ((470) : ℚ) ((471) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_600 (t : ℝ)
    (hlo : ((471) : ℝ) ≤ t) (hhi : t ≤ ((472) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate600
    (fun ht => compactCertificate600_proves ht) ((471) : ℚ) ((472) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_601 (t : ℝ)
    (hlo : ((472) : ℝ) ≤ t) (hhi : t ≤ ((473) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate601
    (fun ht => compactCertificate601_proves ht) ((472) : ℚ) ((473) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_602 (t : ℝ)
    (hlo : ((473) : ℝ) ≤ t) (hhi : t ≤ ((474) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate602
    (fun ht => compactCertificate602_proves ht) ((473) : ℚ) ((474) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_603 (t : ℝ)
    (hlo : ((474) : ℝ) ≤ t) (hhi : t ≤ ((475) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate603
    (fun ht => compactCertificate603_proves ht) ((474) : ℚ) ((475) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_604 (t : ℝ)
    (hlo : ((475) : ℝ) ≤ t) (hhi : t ≤ ((476) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate604
    (fun ht => compactCertificate604_proves ht) ((475) : ℚ) ((476) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_605 (t : ℝ)
    (hlo : ((476) : ℝ) ≤ t) (hhi : t ≤ ((477) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate605
    (fun ht => compactCertificate605_proves ht) ((476) : ℚ) ((477) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_606 (t : ℝ)
    (hlo : ((477) : ℝ) ≤ t) (hhi : t ≤ ((478) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate606
    (fun ht => compactCertificate606_proves ht) ((477) : ℚ) ((478) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_607 (t : ℝ)
    (hlo : ((478) : ℝ) ≤ t) (hhi : t ≤ ((479) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate607
    (fun ht => compactCertificate607_proves ht) ((478) : ℚ) ((479) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_608 (t : ℝ)
    (hlo : ((479) : ℝ) ≤ t) (hhi : t ≤ ((480) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate608
    (fun ht => compactCertificate608_proves ht) ((479) : ℚ) ((480) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_609 (t : ℝ)
    (hlo : ((480) : ℝ) ≤ t) (hhi : t ≤ ((481) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate609
    (fun ht => compactCertificate609_proves ht) ((480) : ℚ) ((481) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_610 (t : ℝ)
    (hlo : ((481) : ℝ) ≤ t) (hhi : t ≤ ((482) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate610
    (fun ht => compactCertificate610_proves ht) ((481) : ℚ) ((482) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_611 (t : ℝ)
    (hlo : ((482) : ℝ) ≤ t) (hhi : t ≤ ((483) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate611
    (fun ht => compactCertificate611_proves ht) ((482) : ℚ) ((483) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_612 (t : ℝ)
    (hlo : ((483) : ℝ) ≤ t) (hhi : t ≤ ((484) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate612
    (fun ht => compactCertificate612_proves ht) ((483) : ℚ) ((484) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_613 (t : ℝ)
    (hlo : ((484) : ℝ) ≤ t) (hhi : t ≤ ((485) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate613
    (fun ht => compactCertificate613_proves ht) ((484) : ℚ) ((485) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_614 (t : ℝ)
    (hlo : ((485) : ℝ) ≤ t) (hhi : t ≤ ((486) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate614
    (fun ht => compactCertificate614_proves ht) ((485) : ℚ) ((486) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_615 (t : ℝ)
    (hlo : ((486) : ℝ) ≤ t) (hhi : t ≤ ((487) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate615
    (fun ht => compactCertificate615_proves ht) ((486) : ℚ) ((487) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_616 (t : ℝ)
    (hlo : ((487) : ℝ) ≤ t) (hhi : t ≤ ((488) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate616
    (fun ht => compactCertificate616_proves ht) ((487) : ℚ) ((488) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_617 (t : ℝ)
    (hlo : ((488) : ℝ) ≤ t) (hhi : t ≤ ((489) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate617
    (fun ht => compactCertificate617_proves ht) ((488) : ℚ) ((489) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_618 (t : ℝ)
    (hlo : ((489) : ℝ) ≤ t) (hhi : t ≤ ((490) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate618
    (fun ht => compactCertificate618_proves ht) ((489) : ℚ) ((490) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_619 (t : ℝ)
    (hlo : ((490) : ℝ) ≤ t) (hhi : t ≤ ((491) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate619
    (fun ht => compactCertificate619_proves ht) ((490) : ℚ) ((491) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_620 (t : ℝ)
    (hlo : ((491) : ℝ) ≤ t) (hhi : t ≤ ((492) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate620
    (fun ht => compactCertificate620_proves ht) ((491) : ℚ) ((492) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_621 (t : ℝ)
    (hlo : ((492) : ℝ) ≤ t) (hhi : t ≤ ((493) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate621
    (fun ht => compactCertificate621_proves ht) ((492) : ℚ) ((493) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_622 (t : ℝ)
    (hlo : ((493) : ℝ) ≤ t) (hhi : t ≤ ((494) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate622
    (fun ht => compactCertificate622_proves ht) ((493) : ℚ) ((494) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_623 (t : ℝ)
    (hlo : ((494) : ℝ) ≤ t) (hhi : t ≤ ((495) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate623
    (fun ht => compactCertificate623_proves ht) ((494) : ℚ) ((495) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_624 (t : ℝ)
    (hlo : ((495) : ℝ) ≤ t) (hhi : t ≤ ((496) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate624
    (fun ht => compactCertificate624_proves ht) ((495) : ℚ) ((496) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_625 (t : ℝ)
    (hlo : ((496) : ℝ) ≤ t) (hhi : t ≤ ((497) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate625
    (fun ht => compactCertificate625_proves ht) ((496) : ℚ) ((497) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_626 (t : ℝ)
    (hlo : ((497) : ℝ) ≤ t) (hhi : t ≤ ((498) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate626
    (fun ht => compactCertificate626_proves ht) ((497) : ℚ) ((498) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_627 (t : ℝ)
    (hlo : ((498) : ℝ) ≤ t) (hhi : t ≤ ((499) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate627
    (fun ht => compactCertificate627_proves ht) ((498) : ℚ) ((499) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_628 (t : ℝ)
    (hlo : ((499) : ℝ) ≤ t) (hhi : t ≤ ((500) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  exact compactCertificate_proves_between compactCertificate628
    (fun ht => compactCertificate628_proves ht) ((499) : ℚ) ((500) : ℚ)
    (by norm_num) rfl t
    (by norm_num at hlo ⊢; exact hlo) (by norm_num at hhi ⊢; exact hhi)

private theorem dual_spectral_compact_group_000_009 (t : ℝ)
    (hlo : ((0) : ℝ) ≤ t) (hhi : t ≤ ((13 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h000 : t ≤ ((1 / 64) : ℝ)
  · exact dual_spectral_compact_000 t hlo h000
  by_cases h001 : t ≤ ((1 / 32) : ℝ)
  · exact dual_spectral_compact_001 t (le_of_not_ge h000) h001
  by_cases h002 : t ≤ ((1 / 16) : ℝ)
  · exact dual_spectral_compact_002 t (le_of_not_ge h001) h002
  by_cases h003 : t ≤ ((1 / 8) : ℝ)
  · exact dual_spectral_compact_003 t (le_of_not_ge h002) h003
  by_cases h004 : t ≤ ((1 / 4) : ℝ)
  · exact dual_spectral_compact_004 t (le_of_not_ge h003) h004
  by_cases h005 : t ≤ ((1 / 2) : ℝ)
  · exact dual_spectral_compact_005 t (le_of_not_ge h004) h005
  by_cases h006 : t ≤ ((1) : ℝ)
  · exact dual_spectral_compact_006 t (le_of_not_ge h005) h006
  by_cases h007 : t ≤ ((2) : ℝ)
  · exact dual_spectral_compact_007 t (le_of_not_ge h006) h007
  by_cases h008 : t ≤ ((3) : ℝ)
  · exact dual_spectral_compact_008 t (le_of_not_ge h007) h008
  · exact dual_spectral_compact_009 t (le_of_not_ge h008) hhi

private theorem dual_spectral_compact_group_010_019 (t : ℝ)
    (hlo : ((13 / 4) : ℝ) ≤ t) (hhi : t ≤ ((9 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h010 : t ≤ ((7 / 2) : ℝ)
  · exact dual_spectral_compact_010 t hlo h010
  by_cases h011 : t ≤ ((29 / 8) : ℝ)
  · exact dual_spectral_compact_011 t (le_of_not_ge h010) h011
  by_cases h012 : t ≤ ((59 / 16) : ℝ)
  · exact dual_spectral_compact_012 t (le_of_not_ge h011) h012
  by_cases h013 : t ≤ ((119 / 32) : ℝ)
  · exact dual_spectral_compact_013 t (le_of_not_ge h012) h013
  by_cases h014 : t ≤ ((15 / 4) : ℝ)
  · exact dual_spectral_compact_014 t (le_of_not_ge h013) h014
  by_cases h015 : t ≤ ((121 / 32) : ℝ)
  · exact dual_spectral_compact_015 t (le_of_not_ge h014) h015
  by_cases h016 : t ≤ ((61 / 16) : ℝ)
  · exact dual_spectral_compact_016 t (le_of_not_ge h015) h016
  by_cases h017 : t ≤ ((31 / 8) : ℝ)
  · exact dual_spectral_compact_017 t (le_of_not_ge h016) h017
  by_cases h018 : t ≤ ((4) : ℝ)
  · exact dual_spectral_compact_018 t (le_of_not_ge h017) h018
  · exact dual_spectral_compact_019 t (le_of_not_ge h018) hhi

private theorem dual_spectral_compact_group_020_029 (t : ℝ)
    (hlo : ((9 / 2) : ℝ) ≤ t) (hhi : t ≤ ((51 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h020 : t ≤ ((5) : ℝ)
  · exact dual_spectral_compact_020 t hlo h020
  by_cases h021 : t ≤ ((11 / 2) : ℝ)
  · exact dual_spectral_compact_021 t (le_of_not_ge h020) h021
  by_cases h022 : t ≤ ((6) : ℝ)
  · exact dual_spectral_compact_022 t (le_of_not_ge h021) h022
  by_cases h023 : t ≤ ((49 / 8) : ℝ)
  · exact dual_spectral_compact_023 t (le_of_not_ge h022) h023
  by_cases h024 : t ≤ ((99 / 16) : ℝ)
  · exact dual_spectral_compact_024 t (le_of_not_ge h023) h024
  by_cases h025 : t ≤ ((25 / 4) : ℝ)
  · exact dual_spectral_compact_025 t (le_of_not_ge h024) h025
  by_cases h026 : t ≤ ((201 / 32) : ℝ)
  · exact dual_spectral_compact_026 t (le_of_not_ge h025) h026
  by_cases h027 : t ≤ ((101 / 16) : ℝ)
  · exact dual_spectral_compact_027 t (le_of_not_ge h026) h027
  by_cases h028 : t ≤ ((203 / 32) : ℝ)
  · exact dual_spectral_compact_028 t (le_of_not_ge h027) h028
  · exact dual_spectral_compact_029 t (le_of_not_ge h028) hhi

private theorem dual_spectral_compact_group_030_039 (t : ℝ)
    (hlo : ((51 / 8) : ℝ) ≤ t) (hhi : t ≤ ((81 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h030 : t ≤ ((103 / 16) : ℝ)
  · exact dual_spectral_compact_030 t hlo h030
  by_cases h031 : t ≤ ((13 / 2) : ℝ)
  · exact dual_spectral_compact_031 t (le_of_not_ge h030) h031
  by_cases h032 : t ≤ ((27 / 4) : ℝ)
  · exact dual_spectral_compact_032 t (le_of_not_ge h031) h032
  by_cases h033 : t ≤ ((7) : ℝ)
  · exact dual_spectral_compact_033 t (le_of_not_ge h032) h033
  by_cases h034 : t ≤ ((8) : ℝ)
  · exact dual_spectral_compact_034 t (le_of_not_ge h033) h034
  by_cases h035 : t ≤ ((9) : ℝ)
  · exact dual_spectral_compact_035 t (le_of_not_ge h034) h035
  by_cases h036 : t ≤ ((19 / 2) : ℝ)
  · exact dual_spectral_compact_036 t (le_of_not_ge h035) h036
  by_cases h037 : t ≤ ((39 / 4) : ℝ)
  · exact dual_spectral_compact_037 t (le_of_not_ge h036) h037
  by_cases h038 : t ≤ ((10) : ℝ)
  · exact dual_spectral_compact_038 t (le_of_not_ge h037) h038
  · exact dual_spectral_compact_039 t (le_of_not_ge h038) hhi

private theorem dual_spectral_compact_group_040_049 (t : ℝ)
    (hlo : ((81 / 8) : ℝ) ≤ t) (hhi : t ≤ ((23 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h040 : t ≤ ((163 / 16) : ℝ)
  · exact dual_spectral_compact_040 t hlo h040
  by_cases h041 : t ≤ ((41 / 4) : ℝ)
  · exact dual_spectral_compact_041 t (le_of_not_ge h040) h041
  by_cases h042 : t ≤ ((329 / 32) : ℝ)
  · exact dual_spectral_compact_042 t (le_of_not_ge h041) h042
  by_cases h043 : t ≤ ((165 / 16) : ℝ)
  · exact dual_spectral_compact_043 t (le_of_not_ge h042) h043
  by_cases h044 : t ≤ ((331 / 32) : ℝ)
  · exact dual_spectral_compact_044 t (le_of_not_ge h043) h044
  by_cases h045 : t ≤ ((83 / 8) : ℝ)
  · exact dual_spectral_compact_045 t (le_of_not_ge h044) h045
  by_cases h046 : t ≤ ((21 / 2) : ℝ)
  · exact dual_spectral_compact_046 t (le_of_not_ge h045) h046
  by_cases h047 : t ≤ ((43 / 4) : ℝ)
  · exact dual_spectral_compact_047 t (le_of_not_ge h046) h047
  by_cases h048 : t ≤ ((11) : ℝ)
  · exact dual_spectral_compact_048 t (le_of_not_ge h047) h048
  · exact dual_spectral_compact_049 t (le_of_not_ge h048) hhi

private theorem dual_spectral_compact_group_050_059 (t : ℝ)
    (hlo : ((23 / 2) : ℝ) ≤ t) (hhi : t ≤ ((539 / 32) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h050 : t ≤ ((12) : ℝ)
  · exact dual_spectral_compact_050 t hlo h050
  by_cases h051 : t ≤ ((13) : ℝ)
  · exact dual_spectral_compact_051 t (le_of_not_ge h050) h051
  by_cases h052 : t ≤ ((14) : ℝ)
  · exact dual_spectral_compact_052 t (le_of_not_ge h051) h052
  by_cases h053 : t ≤ ((15) : ℝ)
  · exact dual_spectral_compact_053 t (le_of_not_ge h052) h053
  by_cases h054 : t ≤ ((31 / 2) : ℝ)
  · exact dual_spectral_compact_054 t (le_of_not_ge h053) h054
  by_cases h055 : t ≤ ((16) : ℝ)
  · exact dual_spectral_compact_055 t (le_of_not_ge h054) h055
  by_cases h056 : t ≤ ((33 / 2) : ℝ)
  · exact dual_spectral_compact_056 t (le_of_not_ge h055) h056
  by_cases h057 : t ≤ ((67 / 4) : ℝ)
  · exact dual_spectral_compact_057 t (le_of_not_ge h056) h057
  by_cases h058 : t ≤ ((269 / 16) : ℝ)
  · exact dual_spectral_compact_058 t (le_of_not_ge h057) h058
  · exact dual_spectral_compact_059 t (le_of_not_ge h058) hhi

private theorem dual_spectral_compact_group_060_069 (t : ℝ)
    (hlo : ((539 / 32) : ℝ) ≤ t) (hhi : t ≤ ((20) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h060 : t ≤ ((135 / 8) : ℝ)
  · exact dual_spectral_compact_060 t hlo h060
  by_cases h061 : t ≤ ((541 / 32) : ℝ)
  · exact dual_spectral_compact_061 t (le_of_not_ge h060) h061
  by_cases h062 : t ≤ ((271 / 16) : ℝ)
  · exact dual_spectral_compact_062 t (le_of_not_ge h061) h062
  by_cases h063 : t ≤ ((17) : ℝ)
  · exact dual_spectral_compact_063 t (le_of_not_ge h062) h063
  by_cases h064 : t ≤ ((137 / 8) : ℝ)
  · exact dual_spectral_compact_064 t (le_of_not_ge h063) h064
  by_cases h065 : t ≤ ((69 / 4) : ℝ)
  · exact dual_spectral_compact_065 t (le_of_not_ge h064) h065
  by_cases h066 : t ≤ ((35 / 2) : ℝ)
  · exact dual_spectral_compact_066 t (le_of_not_ge h065) h066
  by_cases h067 : t ≤ ((18) : ℝ)
  · exact dual_spectral_compact_067 t (le_of_not_ge h066) h067
  by_cases h068 : t ≤ ((19) : ℝ)
  · exact dual_spectral_compact_068 t (le_of_not_ge h067) h068
  · exact dual_spectral_compact_069 t (le_of_not_ge h068) hhi

private theorem dual_spectral_compact_group_070_079 (t : ℝ)
    (hlo : ((20) : ℝ) ≤ t) (hhi : t ≤ ((187 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h070 : t ≤ ((21) : ℝ)
  · exact dual_spectral_compact_070 t hlo h070
  by_cases h071 : t ≤ ((22) : ℝ)
  · exact dual_spectral_compact_071 t (le_of_not_ge h070) h071
  by_cases h072 : t ≤ ((45 / 2) : ℝ)
  · exact dual_spectral_compact_072 t (le_of_not_ge h071) h072
  by_cases h073 : t ≤ ((23) : ℝ)
  · exact dual_spectral_compact_073 t (le_of_not_ge h072) h073
  by_cases h074 : t ≤ ((185 / 8) : ℝ)
  · exact dual_spectral_compact_074 t (le_of_not_ge h073) h074
  by_cases h075 : t ≤ ((93 / 4) : ℝ)
  · exact dual_spectral_compact_075 t (le_of_not_ge h074) h075
  by_cases h076 : t ≤ ((745 / 32) : ℝ)
  · exact dual_spectral_compact_076 t (le_of_not_ge h075) h076
  by_cases h077 : t ≤ ((373 / 16) : ℝ)
  · exact dual_spectral_compact_077 t (le_of_not_ge h076) h077
  by_cases h078 : t ≤ ((747 / 32) : ℝ)
  · exact dual_spectral_compact_078 t (le_of_not_ge h077) h078
  · exact dual_spectral_compact_079 t (le_of_not_ge h078) hhi

private theorem dual_spectral_compact_group_080_089 (t : ℝ)
    (hlo : ((187 / 8) : ℝ) ≤ t) (hhi : t ≤ ((28) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h080 : t ≤ ((749 / 32) : ℝ)
  · exact dual_spectral_compact_080 t hlo h080
  by_cases h081 : t ≤ ((375 / 16) : ℝ)
  · exact dual_spectral_compact_081 t (le_of_not_ge h080) h081
  by_cases h082 : t ≤ ((47 / 2) : ℝ)
  · exact dual_spectral_compact_082 t (le_of_not_ge h081) h082
  by_cases h083 : t ≤ ((189 / 8) : ℝ)
  · exact dual_spectral_compact_083 t (le_of_not_ge h082) h083
  by_cases h084 : t ≤ ((95 / 4) : ℝ)
  · exact dual_spectral_compact_084 t (le_of_not_ge h083) h084
  by_cases h085 : t ≤ ((24) : ℝ)
  · exact dual_spectral_compact_085 t (le_of_not_ge h084) h085
  by_cases h086 : t ≤ ((25) : ℝ)
  · exact dual_spectral_compact_086 t (le_of_not_ge h085) h086
  by_cases h087 : t ≤ ((26) : ℝ)
  · exact dual_spectral_compact_087 t (le_of_not_ge h086) h087
  by_cases h088 : t ≤ ((27) : ℝ)
  · exact dual_spectral_compact_088 t (le_of_not_ge h087) h088
  · exact dual_spectral_compact_089 t (le_of_not_ge h088) hhi

private theorem dual_spectral_compact_group_090_099 (t : ℝ)
    (hlo : ((28) : ℝ) ≤ t) (hhi : t ≤ ((117 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h090 : t ≤ ((57 / 2) : ℝ)
  · exact dual_spectral_compact_090 t hlo h090
  by_cases h091 : t ≤ ((115 / 4) : ℝ)
  · exact dual_spectral_compact_091 t (le_of_not_ge h090) h091
  by_cases h092 : t ≤ ((231 / 8) : ℝ)
  · exact dual_spectral_compact_092 t (le_of_not_ge h091) h092
  by_cases h093 : t ≤ ((29) : ℝ)
  · exact dual_spectral_compact_093 t (le_of_not_ge h092) h093
  by_cases h094 : t ≤ ((465 / 16) : ℝ)
  · exact dual_spectral_compact_094 t (le_of_not_ge h093) h094
  by_cases h095 : t ≤ ((931 / 32) : ℝ)
  · exact dual_spectral_compact_095 t (le_of_not_ge h094) h095
  by_cases h096 : t ≤ ((233 / 8) : ℝ)
  · exact dual_spectral_compact_096 t (le_of_not_ge h095) h096
  by_cases h097 : t ≤ ((933 / 32) : ℝ)
  · exact dual_spectral_compact_097 t (le_of_not_ge h096) h097
  by_cases h098 : t ≤ ((467 / 16) : ℝ)
  · exact dual_spectral_compact_098 t (le_of_not_ge h097) h098
  · exact dual_spectral_compact_099 t (le_of_not_ge h098) hhi

private theorem dual_spectral_compact_group_100_109 (t : ℝ)
    (hlo : ((117 / 4) : ℝ) ≤ t) (hhi : t ≤ ((69 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h100 : t ≤ ((235 / 8) : ℝ)
  · exact dual_spectral_compact_100 t hlo h100
  by_cases h101 : t ≤ ((59 / 2) : ℝ)
  · exact dual_spectral_compact_101 t (le_of_not_ge h100) h101
  by_cases h102 : t ≤ ((30) : ℝ)
  · exact dual_spectral_compact_102 t (le_of_not_ge h101) h102
  by_cases h103 : t ≤ ((61 / 2) : ℝ)
  · exact dual_spectral_compact_103 t (le_of_not_ge h102) h103
  by_cases h104 : t ≤ ((31) : ℝ)
  · exact dual_spectral_compact_104 t (le_of_not_ge h103) h104
  by_cases h105 : t ≤ ((63 / 2) : ℝ)
  · exact dual_spectral_compact_105 t (le_of_not_ge h104) h105
  by_cases h106 : t ≤ ((32) : ℝ)
  · exact dual_spectral_compact_106 t (le_of_not_ge h105) h106
  by_cases h107 : t ≤ ((33) : ℝ)
  · exact dual_spectral_compact_107 t (le_of_not_ge h106) h107
  by_cases h108 : t ≤ ((34) : ℝ)
  · exact dual_spectral_compact_108 t (le_of_not_ge h107) h108
  · exact dual_spectral_compact_109 t (le_of_not_ge h108) hhi

private theorem dual_spectral_compact_group_110_119 (t : ℝ)
    (hlo : ((69 / 2) : ℝ) ≤ t) (hhi : t ≤ ((73 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h110 : t ≤ ((35) : ℝ)
  · exact dual_spectral_compact_110 t hlo h110
  by_cases h111 : t ≤ ((71 / 2) : ℝ)
  · exact dual_spectral_compact_111 t (le_of_not_ge h110) h111
  by_cases h112 : t ≤ ((36) : ℝ)
  · exact dual_spectral_compact_112 t (le_of_not_ge h111) h112
  by_cases h113 : t ≤ ((145 / 4) : ℝ)
  · exact dual_spectral_compact_113 t (le_of_not_ge h112) h113
  by_cases h114 : t ≤ ((581 / 16) : ℝ)
  · exact dual_spectral_compact_114 t (le_of_not_ge h113) h114
  by_cases h115 : t ≤ ((291 / 8) : ℝ)
  · exact dual_spectral_compact_115 t (le_of_not_ge h114) h115
  by_cases h116 : t ≤ ((1165 / 32) : ℝ)
  · exact dual_spectral_compact_116 t (le_of_not_ge h115) h116
  by_cases h117 : t ≤ ((583 / 16) : ℝ)
  · exact dual_spectral_compact_117 t (le_of_not_ge h116) h117
  by_cases h118 : t ≤ ((1167 / 32) : ℝ)
  · exact dual_spectral_compact_118 t (le_of_not_ge h117) h118
  · exact dual_spectral_compact_119 t (le_of_not_ge h118) hhi

private theorem dual_spectral_compact_group_120_129 (t : ℝ)
    (hlo : ((73 / 2) : ℝ) ≤ t) (hhi : t ≤ ((41) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h120 : t ≤ ((585 / 16) : ℝ)
  · exact dual_spectral_compact_120 t hlo h120
  by_cases h121 : t ≤ ((293 / 8) : ℝ)
  · exact dual_spectral_compact_121 t (le_of_not_ge h120) h121
  by_cases h122 : t ≤ ((147 / 4) : ℝ)
  · exact dual_spectral_compact_122 t (le_of_not_ge h121) h122
  by_cases h123 : t ≤ ((37) : ℝ)
  · exact dual_spectral_compact_123 t (le_of_not_ge h122) h123
  by_cases h124 : t ≤ ((75 / 2) : ℝ)
  · exact dual_spectral_compact_124 t (le_of_not_ge h123) h124
  by_cases h125 : t ≤ ((38) : ℝ)
  · exact dual_spectral_compact_125 t (le_of_not_ge h124) h125
  by_cases h126 : t ≤ ((39) : ℝ)
  · exact dual_spectral_compact_126 t (le_of_not_ge h125) h126
  by_cases h127 : t ≤ ((40) : ℝ)
  · exact dual_spectral_compact_127 t (le_of_not_ge h126) h127
  by_cases h128 : t ≤ ((81 / 2) : ℝ)
  · exact dual_spectral_compact_128 t (le_of_not_ge h127) h128
  · exact dual_spectral_compact_129 t (le_of_not_ge h128) hhi

private theorem dual_spectral_compact_group_130_139 (t : ℝ)
    (hlo : ((41) : ℝ) ≤ t) (hhi : t ≤ ((48) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h130 : t ≤ ((83 / 2) : ℝ)
  · exact dual_spectral_compact_130 t hlo h130
  by_cases h131 : t ≤ ((42) : ℝ)
  · exact dual_spectral_compact_131 t (le_of_not_ge h130) h131
  by_cases h132 : t ≤ ((85 / 2) : ℝ)
  · exact dual_spectral_compact_132 t (le_of_not_ge h131) h132
  by_cases h133 : t ≤ ((43) : ℝ)
  · exact dual_spectral_compact_133 t (le_of_not_ge h132) h133
  by_cases h134 : t ≤ ((44) : ℝ)
  · exact dual_spectral_compact_134 t (le_of_not_ge h133) h134
  by_cases h135 : t ≤ ((45) : ℝ)
  · exact dual_spectral_compact_135 t (le_of_not_ge h134) h135
  by_cases h136 : t ≤ ((46) : ℝ)
  · exact dual_spectral_compact_136 t (le_of_not_ge h135) h136
  by_cases h137 : t ≤ ((47) : ℝ)
  · exact dual_spectral_compact_137 t (le_of_not_ge h136) h137
  by_cases h138 : t ≤ ((95 / 2) : ℝ)
  · exact dual_spectral_compact_138 t (le_of_not_ge h137) h138
  · exact dual_spectral_compact_139 t (le_of_not_ge h138) hhi

private theorem dual_spectral_compact_group_140_149 (t : ℝ)
    (hlo : ((48) : ℝ) ≤ t) (hhi : t ≤ ((55) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h140 : t ≤ ((193 / 4) : ℝ)
  · exact dual_spectral_compact_140 t hlo h140
  by_cases h141 : t ≤ ((97 / 2) : ℝ)
  · exact dual_spectral_compact_141 t (le_of_not_ge h140) h141
  by_cases h142 : t ≤ ((49) : ℝ)
  · exact dual_spectral_compact_142 t (le_of_not_ge h141) h142
  by_cases h143 : t ≤ ((50) : ℝ)
  · exact dual_spectral_compact_143 t (le_of_not_ge h142) h143
  by_cases h144 : t ≤ ((51) : ℝ)
  · exact dual_spectral_compact_144 t (le_of_not_ge h143) h144
  by_cases h145 : t ≤ ((103 / 2) : ℝ)
  · exact dual_spectral_compact_145 t (le_of_not_ge h144) h145
  by_cases h146 : t ≤ ((52) : ℝ)
  · exact dual_spectral_compact_146 t (le_of_not_ge h145) h146
  by_cases h147 : t ≤ ((53) : ℝ)
  · exact dual_spectral_compact_147 t (le_of_not_ge h146) h147
  by_cases h148 : t ≤ ((54) : ℝ)
  · exact dual_spectral_compact_148 t (le_of_not_ge h147) h148
  · exact dual_spectral_compact_149 t (le_of_not_ge h148) hhi

private theorem dual_spectral_compact_group_150_159 (t : ℝ)
    (hlo : ((55) : ℝ) ≤ t) (hhi : t ≤ ((62) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h150 : t ≤ ((56) : ℝ)
  · exact dual_spectral_compact_150 t hlo h150
  by_cases h151 : t ≤ ((113 / 2) : ℝ)
  · exact dual_spectral_compact_151 t (le_of_not_ge h150) h151
  by_cases h152 : t ≤ ((57) : ℝ)
  · exact dual_spectral_compact_152 t (le_of_not_ge h151) h152
  by_cases h153 : t ≤ ((58) : ℝ)
  · exact dual_spectral_compact_153 t (le_of_not_ge h152) h153
  by_cases h154 : t ≤ ((59) : ℝ)
  · exact dual_spectral_compact_154 t (le_of_not_ge h153) h154
  by_cases h155 : t ≤ ((119 / 2) : ℝ)
  · exact dual_spectral_compact_155 t (le_of_not_ge h154) h155
  by_cases h156 : t ≤ ((60) : ℝ)
  · exact dual_spectral_compact_156 t (le_of_not_ge h155) h156
  by_cases h157 : t ≤ ((61) : ℝ)
  · exact dual_spectral_compact_157 t (le_of_not_ge h156) h157
  by_cases h158 : t ≤ ((123 / 2) : ℝ)
  · exact dual_spectral_compact_158 t (le_of_not_ge h157) h158
  · exact dual_spectral_compact_159 t (le_of_not_ge h158) hhi

private theorem dual_spectral_compact_group_160_169 (t : ℝ)
    (hlo : ((62) : ℝ) ≤ t) (hhi : t ≤ ((541 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h160 : t ≤ ((63) : ℝ)
  · exact dual_spectral_compact_160 t hlo h160
  by_cases h161 : t ≤ ((64) : ℝ)
  · exact dual_spectral_compact_161 t (le_of_not_ge h160) h161
  by_cases h162 : t ≤ ((65) : ℝ)
  · exact dual_spectral_compact_162 t (le_of_not_ge h161) h162
  by_cases h163 : t ≤ ((66) : ℝ)
  · exact dual_spectral_compact_163 t (le_of_not_ge h162) h163
  by_cases h164 : t ≤ ((133 / 2) : ℝ)
  · exact dual_spectral_compact_164 t (le_of_not_ge h163) h164
  by_cases h165 : t ≤ ((67) : ℝ)
  · exact dual_spectral_compact_165 t (le_of_not_ge h164) h165
  by_cases h166 : t ≤ ((269 / 4) : ℝ)
  · exact dual_spectral_compact_166 t (le_of_not_ge h165) h166
  by_cases h167 : t ≤ ((539 / 8) : ℝ)
  · exact dual_spectral_compact_167 t (le_of_not_ge h166) h167
  by_cases h168 : t ≤ ((135 / 2) : ℝ)
  · exact dual_spectral_compact_168 t (le_of_not_ge h167) h168
  · exact dual_spectral_compact_169 t (le_of_not_ge h168) hhi

private theorem dual_spectral_compact_group_170_179 (t : ℝ)
    (hlo : ((541 / 8) : ℝ) ≤ t) (hhi : t ≤ ((74) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h170 : t ≤ ((271 / 4) : ℝ)
  · exact dual_spectral_compact_170 t hlo h170
  by_cases h171 : t ≤ ((68) : ℝ)
  · exact dual_spectral_compact_171 t (le_of_not_ge h170) h171
  by_cases h172 : t ≤ ((69) : ℝ)
  · exact dual_spectral_compact_172 t (le_of_not_ge h171) h172
  by_cases h173 : t ≤ ((70) : ℝ)
  · exact dual_spectral_compact_173 t (le_of_not_ge h172) h173
  by_cases h174 : t ≤ ((71) : ℝ)
  · exact dual_spectral_compact_174 t (le_of_not_ge h173) h174
  by_cases h175 : t ≤ ((72) : ℝ)
  · exact dual_spectral_compact_175 t (le_of_not_ge h174) h175
  by_cases h176 : t ≤ ((145 / 2) : ℝ)
  · exact dual_spectral_compact_176 t (le_of_not_ge h175) h176
  by_cases h177 : t ≤ ((73) : ℝ)
  · exact dual_spectral_compact_177 t (le_of_not_ge h176) h177
  by_cases h178 : t ≤ ((147 / 2) : ℝ)
  · exact dual_spectral_compact_178 t (le_of_not_ge h177) h178
  · exact dual_spectral_compact_179 t (le_of_not_ge h178) hhi

private theorem dual_spectral_compact_group_180_189 (t : ℝ)
    (hlo : ((74) : ℝ) ≤ t) (hhi : t ≤ ((82) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h180 : t ≤ ((75) : ℝ)
  · exact dual_spectral_compact_180 t hlo h180
  by_cases h181 : t ≤ ((76) : ℝ)
  · exact dual_spectral_compact_181 t (le_of_not_ge h180) h181
  by_cases h182 : t ≤ ((77) : ℝ)
  · exact dual_spectral_compact_182 t (le_of_not_ge h181) h182
  by_cases h183 : t ≤ ((78) : ℝ)
  · exact dual_spectral_compact_183 t (le_of_not_ge h182) h183
  by_cases h184 : t ≤ ((79) : ℝ)
  · exact dual_spectral_compact_184 t (le_of_not_ge h183) h184
  by_cases h185 : t ≤ ((80) : ℝ)
  · exact dual_spectral_compact_185 t (le_of_not_ge h184) h185
  by_cases h186 : t ≤ ((161 / 2) : ℝ)
  · exact dual_spectral_compact_186 t (le_of_not_ge h185) h186
  by_cases h187 : t ≤ ((81) : ℝ)
  · exact dual_spectral_compact_187 t (le_of_not_ge h186) h187
  by_cases h188 : t ≤ ((163 / 2) : ℝ)
  · exact dual_spectral_compact_188 t (le_of_not_ge h187) h188
  · exact dual_spectral_compact_189 t (le_of_not_ge h188) hhi

private theorem dual_spectral_compact_group_190_199 (t : ℝ)
    (hlo : ((82) : ℝ) ≤ t) (hhi : t ≤ ((183 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h190 : t ≤ ((83) : ℝ)
  · exact dual_spectral_compact_190 t hlo h190
  by_cases h191 : t ≤ ((84) : ℝ)
  · exact dual_spectral_compact_191 t (le_of_not_ge h190) h191
  by_cases h192 : t ≤ ((85) : ℝ)
  · exact dual_spectral_compact_192 t (le_of_not_ge h191) h192
  by_cases h193 : t ≤ ((86) : ℝ)
  · exact dual_spectral_compact_193 t (le_of_not_ge h192) h193
  by_cases h194 : t ≤ ((87) : ℝ)
  · exact dual_spectral_compact_194 t (le_of_not_ge h193) h194
  by_cases h195 : t ≤ ((88) : ℝ)
  · exact dual_spectral_compact_195 t (le_of_not_ge h194) h195
  by_cases h196 : t ≤ ((89) : ℝ)
  · exact dual_spectral_compact_196 t (le_of_not_ge h195) h196
  by_cases h197 : t ≤ ((90) : ℝ)
  · exact dual_spectral_compact_197 t (le_of_not_ge h196) h197
  by_cases h198 : t ≤ ((91) : ℝ)
  · exact dual_spectral_compact_198 t (le_of_not_ge h197) h198
  · exact dual_spectral_compact_199 t (le_of_not_ge h198) hhi

private theorem dual_spectral_compact_group_200_209 (t : ℝ)
    (hlo : ((183 / 2) : ℝ) ≤ t) (hhi : t ≤ ((741 / 8) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h200 : t ≤ ((92) : ℝ)
  · exact dual_spectral_compact_200 t hlo h200
  by_cases h201 : t ≤ ((369 / 4) : ℝ)
  · exact dual_spectral_compact_201 t (le_of_not_ge h200) h201
  by_cases h202 : t ≤ ((739 / 8) : ℝ)
  · exact dual_spectral_compact_202 t (le_of_not_ge h201) h202
  by_cases h203 : t ≤ ((2957 / 32) : ℝ)
  · exact dual_spectral_compact_203 t (le_of_not_ge h202) h203
  by_cases h204 : t ≤ ((1479 / 16) : ℝ)
  · exact dual_spectral_compact_204 t (le_of_not_ge h203) h204
  by_cases h205 : t ≤ ((2959 / 32) : ℝ)
  · exact dual_spectral_compact_205 t (le_of_not_ge h204) h205
  by_cases h206 : t ≤ ((185 / 2) : ℝ)
  · exact dual_spectral_compact_206 t (le_of_not_ge h205) h206
  by_cases h207 : t ≤ ((2961 / 32) : ℝ)
  · exact dual_spectral_compact_207 t (le_of_not_ge h206) h207
  by_cases h208 : t ≤ ((1481 / 16) : ℝ)
  · exact dual_spectral_compact_208 t (le_of_not_ge h207) h208
  · exact dual_spectral_compact_209 t (le_of_not_ge h208) hhi

private theorem dual_spectral_compact_group_210_219 (t : ℝ)
    (hlo : ((741 / 8) : ℝ) ≤ t) (hhi : t ≤ ((99) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h210 : t ≤ ((371 / 4) : ℝ)
  · exact dual_spectral_compact_210 t hlo h210
  by_cases h211 : t ≤ ((93) : ℝ)
  · exact dual_spectral_compact_211 t (le_of_not_ge h210) h211
  by_cases h212 : t ≤ ((94) : ℝ)
  · exact dual_spectral_compact_212 t (le_of_not_ge h211) h212
  by_cases h213 : t ≤ ((95) : ℝ)
  · exact dual_spectral_compact_213 t (le_of_not_ge h212) h213
  by_cases h214 : t ≤ ((96) : ℝ)
  · exact dual_spectral_compact_214 t (le_of_not_ge h213) h214
  by_cases h215 : t ≤ ((97) : ℝ)
  · exact dual_spectral_compact_215 t (le_of_not_ge h214) h215
  by_cases h216 : t ≤ ((195 / 2) : ℝ)
  · exact dual_spectral_compact_216 t (le_of_not_ge h215) h216
  by_cases h217 : t ≤ ((98) : ℝ)
  · exact dual_spectral_compact_217 t (le_of_not_ge h216) h217
  by_cases h218 : t ≤ ((197 / 2) : ℝ)
  · exact dual_spectral_compact_218 t (le_of_not_ge h217) h218
  · exact dual_spectral_compact_219 t (le_of_not_ge h218) hhi

private theorem dual_spectral_compact_group_220_229 (t : ℝ)
    (hlo : ((99) : ℝ) ≤ t) (hhi : t ≤ ((107) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h220 : t ≤ ((100) : ℝ)
  · exact dual_spectral_compact_220 t hlo h220
  by_cases h221 : t ≤ ((101) : ℝ)
  · exact dual_spectral_compact_221 t (le_of_not_ge h220) h221
  by_cases h222 : t ≤ ((102) : ℝ)
  · exact dual_spectral_compact_222 t (le_of_not_ge h221) h222
  by_cases h223 : t ≤ ((103) : ℝ)
  · exact dual_spectral_compact_223 t (le_of_not_ge h222) h223
  by_cases h224 : t ≤ ((104) : ℝ)
  · exact dual_spectral_compact_224 t (le_of_not_ge h223) h224
  by_cases h225 : t ≤ ((209 / 2) : ℝ)
  · exact dual_spectral_compact_225 t (le_of_not_ge h224) h225
  by_cases h226 : t ≤ ((105) : ℝ)
  · exact dual_spectral_compact_226 t (le_of_not_ge h225) h226
  by_cases h227 : t ≤ ((211 / 2) : ℝ)
  · exact dual_spectral_compact_227 t (le_of_not_ge h226) h227
  by_cases h228 : t ≤ ((106) : ℝ)
  · exact dual_spectral_compact_228 t (le_of_not_ge h227) h228
  · exact dual_spectral_compact_229 t (le_of_not_ge h228) hhi

private theorem dual_spectral_compact_group_230_239 (t : ℝ)
    (hlo : ((107) : ℝ) ≤ t) (hhi : t ≤ ((233 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h230 : t ≤ ((108) : ℝ)
  · exact dual_spectral_compact_230 t hlo h230
  by_cases h231 : t ≤ ((109) : ℝ)
  · exact dual_spectral_compact_231 t (le_of_not_ge h230) h231
  by_cases h232 : t ≤ ((110) : ℝ)
  · exact dual_spectral_compact_232 t (le_of_not_ge h231) h232
  by_cases h233 : t ≤ ((111) : ℝ)
  · exact dual_spectral_compact_233 t (le_of_not_ge h232) h233
  by_cases h234 : t ≤ ((112) : ℝ)
  · exact dual_spectral_compact_234 t (le_of_not_ge h233) h234
  by_cases h235 : t ≤ ((113) : ℝ)
  · exact dual_spectral_compact_235 t (le_of_not_ge h234) h235
  by_cases h236 : t ≤ ((114) : ℝ)
  · exact dual_spectral_compact_236 t (le_of_not_ge h235) h236
  by_cases h237 : t ≤ ((115) : ℝ)
  · exact dual_spectral_compact_237 t (le_of_not_ge h236) h237
  by_cases h238 : t ≤ ((116) : ℝ)
  · exact dual_spectral_compact_238 t (le_of_not_ge h237) h238
  · exact dual_spectral_compact_239 t (le_of_not_ge h238) hhi

private theorem dual_spectral_compact_group_240_249 (t : ℝ)
    (hlo : ((233 / 2) : ℝ) ≤ t) (hhi : t ≤ ((125) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h240 : t ≤ ((117) : ℝ)
  · exact dual_spectral_compact_240 t hlo h240
  by_cases h241 : t ≤ ((235 / 2) : ℝ)
  · exact dual_spectral_compact_241 t (le_of_not_ge h240) h241
  by_cases h242 : t ≤ ((118) : ℝ)
  · exact dual_spectral_compact_242 t (le_of_not_ge h241) h242
  by_cases h243 : t ≤ ((119) : ℝ)
  · exact dual_spectral_compact_243 t (le_of_not_ge h242) h243
  by_cases h244 : t ≤ ((120) : ℝ)
  · exact dual_spectral_compact_244 t (le_of_not_ge h243) h244
  by_cases h245 : t ≤ ((121) : ℝ)
  · exact dual_spectral_compact_245 t (le_of_not_ge h244) h245
  by_cases h246 : t ≤ ((122) : ℝ)
  · exact dual_spectral_compact_246 t (le_of_not_ge h245) h246
  by_cases h247 : t ≤ ((123) : ℝ)
  · exact dual_spectral_compact_247 t (le_of_not_ge h246) h247
  by_cases h248 : t ≤ ((124) : ℝ)
  · exact dual_spectral_compact_248 t (le_of_not_ge h247) h248
  · exact dual_spectral_compact_249 t (le_of_not_ge h248) hhi

private theorem dual_spectral_compact_group_250_259 (t : ℝ)
    (hlo : ((125) : ℝ) ≤ t) (hhi : t ≤ ((135) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h250 : t ≤ ((126) : ℝ)
  · exact dual_spectral_compact_250 t hlo h250
  by_cases h251 : t ≤ ((127) : ℝ)
  · exact dual_spectral_compact_251 t (le_of_not_ge h250) h251
  by_cases h252 : t ≤ ((128) : ℝ)
  · exact dual_spectral_compact_252 t (le_of_not_ge h251) h252
  by_cases h253 : t ≤ ((129) : ℝ)
  · exact dual_spectral_compact_253 t (le_of_not_ge h252) h253
  by_cases h254 : t ≤ ((130) : ℝ)
  · exact dual_spectral_compact_254 t (le_of_not_ge h253) h254
  by_cases h255 : t ≤ ((131) : ℝ)
  · exact dual_spectral_compact_255 t (le_of_not_ge h254) h255
  by_cases h256 : t ≤ ((132) : ℝ)
  · exact dual_spectral_compact_256 t (le_of_not_ge h255) h256
  by_cases h257 : t ≤ ((133) : ℝ)
  · exact dual_spectral_compact_257 t (le_of_not_ge h256) h257
  by_cases h258 : t ≤ ((134) : ℝ)
  · exact dual_spectral_compact_258 t (le_of_not_ge h257) h258
  · exact dual_spectral_compact_259 t (le_of_not_ge h258) hhi

private theorem dual_spectral_compact_group_260_269 (t : ℝ)
    (hlo : ((135) : ℝ) ≤ t) (hhi : t ≤ ((144) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h260 : t ≤ ((271 / 2) : ℝ)
  · exact dual_spectral_compact_260 t hlo h260
  by_cases h261 : t ≤ ((136) : ℝ)
  · exact dual_spectral_compact_261 t (le_of_not_ge h260) h261
  by_cases h262 : t ≤ ((137) : ℝ)
  · exact dual_spectral_compact_262 t (le_of_not_ge h261) h262
  by_cases h263 : t ≤ ((138) : ℝ)
  · exact dual_spectral_compact_263 t (le_of_not_ge h262) h263
  by_cases h264 : t ≤ ((139) : ℝ)
  · exact dual_spectral_compact_264 t (le_of_not_ge h263) h264
  by_cases h265 : t ≤ ((140) : ℝ)
  · exact dual_spectral_compact_265 t (le_of_not_ge h264) h265
  by_cases h266 : t ≤ ((141) : ℝ)
  · exact dual_spectral_compact_266 t (le_of_not_ge h265) h266
  by_cases h267 : t ≤ ((142) : ℝ)
  · exact dual_spectral_compact_267 t (le_of_not_ge h266) h267
  by_cases h268 : t ≤ ((143) : ℝ)
  · exact dual_spectral_compact_268 t (le_of_not_ge h267) h268
  · exact dual_spectral_compact_269 t (le_of_not_ge h268) hhi

private theorem dual_spectral_compact_group_270_279 (t : ℝ)
    (hlo : ((144) : ℝ) ≤ t) (hhi : t ≤ ((154) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h270 : t ≤ ((145) : ℝ)
  · exact dual_spectral_compact_270 t hlo h270
  by_cases h271 : t ≤ ((146) : ℝ)
  · exact dual_spectral_compact_271 t (le_of_not_ge h270) h271
  by_cases h272 : t ≤ ((147) : ℝ)
  · exact dual_spectral_compact_272 t (le_of_not_ge h271) h272
  by_cases h273 : t ≤ ((148) : ℝ)
  · exact dual_spectral_compact_273 t (le_of_not_ge h272) h273
  by_cases h274 : t ≤ ((149) : ℝ)
  · exact dual_spectral_compact_274 t (le_of_not_ge h273) h274
  by_cases h275 : t ≤ ((150) : ℝ)
  · exact dual_spectral_compact_275 t (le_of_not_ge h274) h275
  by_cases h276 : t ≤ ((151) : ℝ)
  · exact dual_spectral_compact_276 t (le_of_not_ge h275) h276
  by_cases h277 : t ≤ ((152) : ℝ)
  · exact dual_spectral_compact_277 t (le_of_not_ge h276) h277
  by_cases h278 : t ≤ ((153) : ℝ)
  · exact dual_spectral_compact_278 t (le_of_not_ge h277) h278
  · exact dual_spectral_compact_279 t (le_of_not_ge h278) hhi

private theorem dual_spectral_compact_group_280_289 (t : ℝ)
    (hlo : ((154) : ℝ) ≤ t) (hhi : t ≤ ((164) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h280 : t ≤ ((155) : ℝ)
  · exact dual_spectral_compact_280 t hlo h280
  by_cases h281 : t ≤ ((156) : ℝ)
  · exact dual_spectral_compact_281 t (le_of_not_ge h280) h281
  by_cases h282 : t ≤ ((157) : ℝ)
  · exact dual_spectral_compact_282 t (le_of_not_ge h281) h282
  by_cases h283 : t ≤ ((158) : ℝ)
  · exact dual_spectral_compact_283 t (le_of_not_ge h282) h283
  by_cases h284 : t ≤ ((159) : ℝ)
  · exact dual_spectral_compact_284 t (le_of_not_ge h283) h284
  by_cases h285 : t ≤ ((160) : ℝ)
  · exact dual_spectral_compact_285 t (le_of_not_ge h284) h285
  by_cases h286 : t ≤ ((161) : ℝ)
  · exact dual_spectral_compact_286 t (le_of_not_ge h285) h286
  by_cases h287 : t ≤ ((162) : ℝ)
  · exact dual_spectral_compact_287 t (le_of_not_ge h286) h287
  by_cases h288 : t ≤ ((163) : ℝ)
  · exact dual_spectral_compact_288 t (le_of_not_ge h287) h288
  · exact dual_spectral_compact_289 t (le_of_not_ge h288) hhi

private theorem dual_spectral_compact_group_290_299 (t : ℝ)
    (hlo : ((164) : ℝ) ≤ t) (hhi : t ≤ ((173) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h290 : t ≤ ((165) : ℝ)
  · exact dual_spectral_compact_290 t hlo h290
  by_cases h291 : t ≤ ((166) : ℝ)
  · exact dual_spectral_compact_291 t (le_of_not_ge h290) h291
  by_cases h292 : t ≤ ((333 / 2) : ℝ)
  · exact dual_spectral_compact_292 t (le_of_not_ge h291) h292
  by_cases h293 : t ≤ ((167) : ℝ)
  · exact dual_spectral_compact_293 t (le_of_not_ge h292) h293
  by_cases h294 : t ≤ ((168) : ℝ)
  · exact dual_spectral_compact_294 t (le_of_not_ge h293) h294
  by_cases h295 : t ≤ ((169) : ℝ)
  · exact dual_spectral_compact_295 t (le_of_not_ge h294) h295
  by_cases h296 : t ≤ ((170) : ℝ)
  · exact dual_spectral_compact_296 t (le_of_not_ge h295) h296
  by_cases h297 : t ≤ ((171) : ℝ)
  · exact dual_spectral_compact_297 t (le_of_not_ge h296) h297
  by_cases h298 : t ≤ ((172) : ℝ)
  · exact dual_spectral_compact_298 t (le_of_not_ge h297) h298
  · exact dual_spectral_compact_299 t (le_of_not_ge h298) hhi

private theorem dual_spectral_compact_group_300_309 (t : ℝ)
    (hlo : ((173) : ℝ) ≤ t) (hhi : t ≤ ((183) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h300 : t ≤ ((174) : ℝ)
  · exact dual_spectral_compact_300 t hlo h300
  by_cases h301 : t ≤ ((175) : ℝ)
  · exact dual_spectral_compact_301 t (le_of_not_ge h300) h301
  by_cases h302 : t ≤ ((176) : ℝ)
  · exact dual_spectral_compact_302 t (le_of_not_ge h301) h302
  by_cases h303 : t ≤ ((177) : ℝ)
  · exact dual_spectral_compact_303 t (le_of_not_ge h302) h303
  by_cases h304 : t ≤ ((178) : ℝ)
  · exact dual_spectral_compact_304 t (le_of_not_ge h303) h304
  by_cases h305 : t ≤ ((179) : ℝ)
  · exact dual_spectral_compact_305 t (le_of_not_ge h304) h305
  by_cases h306 : t ≤ ((180) : ℝ)
  · exact dual_spectral_compact_306 t (le_of_not_ge h305) h306
  by_cases h307 : t ≤ ((181) : ℝ)
  · exact dual_spectral_compact_307 t (le_of_not_ge h306) h307
  by_cases h308 : t ≤ ((182) : ℝ)
  · exact dual_spectral_compact_308 t (le_of_not_ge h307) h308
  · exact dual_spectral_compact_309 t (le_of_not_ge h308) hhi

private theorem dual_spectral_compact_group_310_319 (t : ℝ)
    (hlo : ((183) : ℝ) ≤ t) (hhi : t ≤ ((192) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h310 : t ≤ ((184) : ℝ)
  · exact dual_spectral_compact_310 t hlo h310
  by_cases h311 : t ≤ ((185) : ℝ)
  · exact dual_spectral_compact_311 t (le_of_not_ge h310) h311
  by_cases h312 : t ≤ ((186) : ℝ)
  · exact dual_spectral_compact_312 t (le_of_not_ge h311) h312
  by_cases h313 : t ≤ ((187) : ℝ)
  · exact dual_spectral_compact_313 t (le_of_not_ge h312) h313
  by_cases h314 : t ≤ ((188) : ℝ)
  · exact dual_spectral_compact_314 t (le_of_not_ge h313) h314
  by_cases h315 : t ≤ ((189) : ℝ)
  · exact dual_spectral_compact_315 t (le_of_not_ge h314) h315
  by_cases h316 : t ≤ ((190) : ℝ)
  · exact dual_spectral_compact_316 t (le_of_not_ge h315) h316
  by_cases h317 : t ≤ ((191) : ℝ)
  · exact dual_spectral_compact_317 t (le_of_not_ge h316) h317
  by_cases h318 : t ≤ ((383 / 2) : ℝ)
  · exact dual_spectral_compact_318 t (le_of_not_ge h317) h318
  · exact dual_spectral_compact_319 t (le_of_not_ge h318) hhi

private theorem dual_spectral_compact_group_320_329 (t : ℝ)
    (hlo : ((192) : ℝ) ≤ t) (hhi : t ≤ ((202) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h320 : t ≤ ((193) : ℝ)
  · exact dual_spectral_compact_320 t hlo h320
  by_cases h321 : t ≤ ((194) : ℝ)
  · exact dual_spectral_compact_321 t (le_of_not_ge h320) h321
  by_cases h322 : t ≤ ((195) : ℝ)
  · exact dual_spectral_compact_322 t (le_of_not_ge h321) h322
  by_cases h323 : t ≤ ((196) : ℝ)
  · exact dual_spectral_compact_323 t (le_of_not_ge h322) h323
  by_cases h324 : t ≤ ((197) : ℝ)
  · exact dual_spectral_compact_324 t (le_of_not_ge h323) h324
  by_cases h325 : t ≤ ((198) : ℝ)
  · exact dual_spectral_compact_325 t (le_of_not_ge h324) h325
  by_cases h326 : t ≤ ((199) : ℝ)
  · exact dual_spectral_compact_326 t (le_of_not_ge h325) h326
  by_cases h327 : t ≤ ((200) : ℝ)
  · exact dual_spectral_compact_327 t (le_of_not_ge h326) h327
  by_cases h328 : t ≤ ((201) : ℝ)
  · exact dual_spectral_compact_328 t (le_of_not_ge h327) h328
  · exact dual_spectral_compact_329 t (le_of_not_ge h328) hhi

private theorem dual_spectral_compact_group_330_339 (t : ℝ)
    (hlo : ((202) : ℝ) ≤ t) (hhi : t ≤ ((212) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h330 : t ≤ ((203) : ℝ)
  · exact dual_spectral_compact_330 t hlo h330
  by_cases h331 : t ≤ ((204) : ℝ)
  · exact dual_spectral_compact_331 t (le_of_not_ge h330) h331
  by_cases h332 : t ≤ ((205) : ℝ)
  · exact dual_spectral_compact_332 t (le_of_not_ge h331) h332
  by_cases h333 : t ≤ ((206) : ℝ)
  · exact dual_spectral_compact_333 t (le_of_not_ge h332) h333
  by_cases h334 : t ≤ ((207) : ℝ)
  · exact dual_spectral_compact_334 t (le_of_not_ge h333) h334
  by_cases h335 : t ≤ ((208) : ℝ)
  · exact dual_spectral_compact_335 t (le_of_not_ge h334) h335
  by_cases h336 : t ≤ ((209) : ℝ)
  · exact dual_spectral_compact_336 t (le_of_not_ge h335) h336
  by_cases h337 : t ≤ ((210) : ℝ)
  · exact dual_spectral_compact_337 t (le_of_not_ge h336) h337
  by_cases h338 : t ≤ ((211) : ℝ)
  · exact dual_spectral_compact_338 t (le_of_not_ge h337) h338
  · exact dual_spectral_compact_339 t (le_of_not_ge h338) hhi

private theorem dual_spectral_compact_group_340_349 (t : ℝ)
    (hlo : ((212) : ℝ) ≤ t) (hhi : t ≤ ((221) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h340 : t ≤ ((213) : ℝ)
  · exact dual_spectral_compact_340 t hlo h340
  by_cases h341 : t ≤ ((214) : ℝ)
  · exact dual_spectral_compact_341 t (le_of_not_ge h340) h341
  by_cases h342 : t ≤ ((215) : ℝ)
  · exact dual_spectral_compact_342 t (le_of_not_ge h341) h342
  by_cases h343 : t ≤ ((216) : ℝ)
  · exact dual_spectral_compact_343 t (le_of_not_ge h342) h343
  by_cases h344 : t ≤ ((433 / 2) : ℝ)
  · exact dual_spectral_compact_344 t (le_of_not_ge h343) h344
  by_cases h345 : t ≤ ((217) : ℝ)
  · exact dual_spectral_compact_345 t (le_of_not_ge h344) h345
  by_cases h346 : t ≤ ((218) : ℝ)
  · exact dual_spectral_compact_346 t (le_of_not_ge h345) h346
  by_cases h347 : t ≤ ((219) : ℝ)
  · exact dual_spectral_compact_347 t (le_of_not_ge h346) h347
  by_cases h348 : t ≤ ((220) : ℝ)
  · exact dual_spectral_compact_348 t (le_of_not_ge h347) h348
  · exact dual_spectral_compact_349 t (le_of_not_ge h348) hhi

private theorem dual_spectral_compact_group_350_359 (t : ℝ)
    (hlo : ((221) : ℝ) ≤ t) (hhi : t ≤ ((231) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h350 : t ≤ ((222) : ℝ)
  · exact dual_spectral_compact_350 t hlo h350
  by_cases h351 : t ≤ ((223) : ℝ)
  · exact dual_spectral_compact_351 t (le_of_not_ge h350) h351
  by_cases h352 : t ≤ ((224) : ℝ)
  · exact dual_spectral_compact_352 t (le_of_not_ge h351) h352
  by_cases h353 : t ≤ ((225) : ℝ)
  · exact dual_spectral_compact_353 t (le_of_not_ge h352) h353
  by_cases h354 : t ≤ ((226) : ℝ)
  · exact dual_spectral_compact_354 t (le_of_not_ge h353) h354
  by_cases h355 : t ≤ ((227) : ℝ)
  · exact dual_spectral_compact_355 t (le_of_not_ge h354) h355
  by_cases h356 : t ≤ ((228) : ℝ)
  · exact dual_spectral_compact_356 t (le_of_not_ge h355) h356
  by_cases h357 : t ≤ ((229) : ℝ)
  · exact dual_spectral_compact_357 t (le_of_not_ge h356) h357
  by_cases h358 : t ≤ ((230) : ℝ)
  · exact dual_spectral_compact_358 t (le_of_not_ge h357) h358
  · exact dual_spectral_compact_359 t (le_of_not_ge h358) hhi

private theorem dual_spectral_compact_group_360_369 (t : ℝ)
    (hlo : ((231) : ℝ) ≤ t) (hhi : t ≤ ((241) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h360 : t ≤ ((232) : ℝ)
  · exact dual_spectral_compact_360 t hlo h360
  by_cases h361 : t ≤ ((233) : ℝ)
  · exact dual_spectral_compact_361 t (le_of_not_ge h360) h361
  by_cases h362 : t ≤ ((234) : ℝ)
  · exact dual_spectral_compact_362 t (le_of_not_ge h361) h362
  by_cases h363 : t ≤ ((235) : ℝ)
  · exact dual_spectral_compact_363 t (le_of_not_ge h362) h363
  by_cases h364 : t ≤ ((236) : ℝ)
  · exact dual_spectral_compact_364 t (le_of_not_ge h363) h364
  by_cases h365 : t ≤ ((237) : ℝ)
  · exact dual_spectral_compact_365 t (le_of_not_ge h364) h365
  by_cases h366 : t ≤ ((238) : ℝ)
  · exact dual_spectral_compact_366 t (le_of_not_ge h365) h366
  by_cases h367 : t ≤ ((239) : ℝ)
  · exact dual_spectral_compact_367 t (le_of_not_ge h366) h367
  by_cases h368 : t ≤ ((240) : ℝ)
  · exact dual_spectral_compact_368 t (le_of_not_ge h367) h368
  · exact dual_spectral_compact_369 t (le_of_not_ge h368) hhi

private theorem dual_spectral_compact_group_370_379 (t : ℝ)
    (hlo : ((241) : ℝ) ≤ t) (hhi : t ≤ ((251) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h370 : t ≤ ((242) : ℝ)
  · exact dual_spectral_compact_370 t hlo h370
  by_cases h371 : t ≤ ((243) : ℝ)
  · exact dual_spectral_compact_371 t (le_of_not_ge h370) h371
  by_cases h372 : t ≤ ((244) : ℝ)
  · exact dual_spectral_compact_372 t (le_of_not_ge h371) h372
  by_cases h373 : t ≤ ((245) : ℝ)
  · exact dual_spectral_compact_373 t (le_of_not_ge h372) h373
  by_cases h374 : t ≤ ((246) : ℝ)
  · exact dual_spectral_compact_374 t (le_of_not_ge h373) h374
  by_cases h375 : t ≤ ((247) : ℝ)
  · exact dual_spectral_compact_375 t (le_of_not_ge h374) h375
  by_cases h376 : t ≤ ((248) : ℝ)
  · exact dual_spectral_compact_376 t (le_of_not_ge h375) h376
  by_cases h377 : t ≤ ((249) : ℝ)
  · exact dual_spectral_compact_377 t (le_of_not_ge h376) h377
  by_cases h378 : t ≤ ((250) : ℝ)
  · exact dual_spectral_compact_378 t (le_of_not_ge h377) h378
  · exact dual_spectral_compact_379 t (le_of_not_ge h378) hhi

private theorem dual_spectral_compact_group_380_389 (t : ℝ)
    (hlo : ((251) : ℝ) ≤ t) (hhi : t ≤ ((261) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h380 : t ≤ ((252) : ℝ)
  · exact dual_spectral_compact_380 t hlo h380
  by_cases h381 : t ≤ ((253) : ℝ)
  · exact dual_spectral_compact_381 t (le_of_not_ge h380) h381
  by_cases h382 : t ≤ ((254) : ℝ)
  · exact dual_spectral_compact_382 t (le_of_not_ge h381) h382
  by_cases h383 : t ≤ ((255) : ℝ)
  · exact dual_spectral_compact_383 t (le_of_not_ge h382) h383
  by_cases h384 : t ≤ ((256) : ℝ)
  · exact dual_spectral_compact_384 t (le_of_not_ge h383) h384
  by_cases h385 : t ≤ ((257) : ℝ)
  · exact dual_spectral_compact_385 t (le_of_not_ge h384) h385
  by_cases h386 : t ≤ ((258) : ℝ)
  · exact dual_spectral_compact_386 t (le_of_not_ge h385) h386
  by_cases h387 : t ≤ ((259) : ℝ)
  · exact dual_spectral_compact_387 t (le_of_not_ge h386) h387
  by_cases h388 : t ≤ ((260) : ℝ)
  · exact dual_spectral_compact_388 t (le_of_not_ge h387) h388
  · exact dual_spectral_compact_389 t (le_of_not_ge h388) hhi

private theorem dual_spectral_compact_group_390_399 (t : ℝ)
    (hlo : ((261) : ℝ) ≤ t) (hhi : t ≤ ((271) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h390 : t ≤ ((262) : ℝ)
  · exact dual_spectral_compact_390 t hlo h390
  by_cases h391 : t ≤ ((263) : ℝ)
  · exact dual_spectral_compact_391 t (le_of_not_ge h390) h391
  by_cases h392 : t ≤ ((264) : ℝ)
  · exact dual_spectral_compact_392 t (le_of_not_ge h391) h392
  by_cases h393 : t ≤ ((265) : ℝ)
  · exact dual_spectral_compact_393 t (le_of_not_ge h392) h393
  by_cases h394 : t ≤ ((266) : ℝ)
  · exact dual_spectral_compact_394 t (le_of_not_ge h393) h394
  by_cases h395 : t ≤ ((267) : ℝ)
  · exact dual_spectral_compact_395 t (le_of_not_ge h394) h395
  by_cases h396 : t ≤ ((268) : ℝ)
  · exact dual_spectral_compact_396 t (le_of_not_ge h395) h396
  by_cases h397 : t ≤ ((269) : ℝ)
  · exact dual_spectral_compact_397 t (le_of_not_ge h396) h397
  by_cases h398 : t ≤ ((270) : ℝ)
  · exact dual_spectral_compact_398 t (le_of_not_ge h397) h398
  · exact dual_spectral_compact_399 t (le_of_not_ge h398) hhi

private theorem dual_spectral_compact_group_400_409 (t : ℝ)
    (hlo : ((271) : ℝ) ≤ t) (hhi : t ≤ ((281) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h400 : t ≤ ((272) : ℝ)
  · exact dual_spectral_compact_400 t hlo h400
  by_cases h401 : t ≤ ((273) : ℝ)
  · exact dual_spectral_compact_401 t (le_of_not_ge h400) h401
  by_cases h402 : t ≤ ((274) : ℝ)
  · exact dual_spectral_compact_402 t (le_of_not_ge h401) h402
  by_cases h403 : t ≤ ((275) : ℝ)
  · exact dual_spectral_compact_403 t (le_of_not_ge h402) h403
  by_cases h404 : t ≤ ((276) : ℝ)
  · exact dual_spectral_compact_404 t (le_of_not_ge h403) h404
  by_cases h405 : t ≤ ((277) : ℝ)
  · exact dual_spectral_compact_405 t (le_of_not_ge h404) h405
  by_cases h406 : t ≤ ((278) : ℝ)
  · exact dual_spectral_compact_406 t (le_of_not_ge h405) h406
  by_cases h407 : t ≤ ((279) : ℝ)
  · exact dual_spectral_compact_407 t (le_of_not_ge h406) h407
  by_cases h408 : t ≤ ((280) : ℝ)
  · exact dual_spectral_compact_408 t (le_of_not_ge h407) h408
  · exact dual_spectral_compact_409 t (le_of_not_ge h408) hhi

private theorem dual_spectral_compact_group_410_419 (t : ℝ)
    (hlo : ((281) : ℝ) ≤ t) (hhi : t ≤ ((291) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h410 : t ≤ ((282) : ℝ)
  · exact dual_spectral_compact_410 t hlo h410
  by_cases h411 : t ≤ ((283) : ℝ)
  · exact dual_spectral_compact_411 t (le_of_not_ge h410) h411
  by_cases h412 : t ≤ ((284) : ℝ)
  · exact dual_spectral_compact_412 t (le_of_not_ge h411) h412
  by_cases h413 : t ≤ ((285) : ℝ)
  · exact dual_spectral_compact_413 t (le_of_not_ge h412) h413
  by_cases h414 : t ≤ ((286) : ℝ)
  · exact dual_spectral_compact_414 t (le_of_not_ge h413) h414
  by_cases h415 : t ≤ ((287) : ℝ)
  · exact dual_spectral_compact_415 t (le_of_not_ge h414) h415
  by_cases h416 : t ≤ ((288) : ℝ)
  · exact dual_spectral_compact_416 t (le_of_not_ge h415) h416
  by_cases h417 : t ≤ ((289) : ℝ)
  · exact dual_spectral_compact_417 t (le_of_not_ge h416) h417
  by_cases h418 : t ≤ ((290) : ℝ)
  · exact dual_spectral_compact_418 t (le_of_not_ge h417) h418
  · exact dual_spectral_compact_419 t (le_of_not_ge h418) hhi

private theorem dual_spectral_compact_group_420_429 (t : ℝ)
    (hlo : ((291) : ℝ) ≤ t) (hhi : t ≤ ((301) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h420 : t ≤ ((292) : ℝ)
  · exact dual_spectral_compact_420 t hlo h420
  by_cases h421 : t ≤ ((293) : ℝ)
  · exact dual_spectral_compact_421 t (le_of_not_ge h420) h421
  by_cases h422 : t ≤ ((294) : ℝ)
  · exact dual_spectral_compact_422 t (le_of_not_ge h421) h422
  by_cases h423 : t ≤ ((295) : ℝ)
  · exact dual_spectral_compact_423 t (le_of_not_ge h422) h423
  by_cases h424 : t ≤ ((296) : ℝ)
  · exact dual_spectral_compact_424 t (le_of_not_ge h423) h424
  by_cases h425 : t ≤ ((297) : ℝ)
  · exact dual_spectral_compact_425 t (le_of_not_ge h424) h425
  by_cases h426 : t ≤ ((298) : ℝ)
  · exact dual_spectral_compact_426 t (le_of_not_ge h425) h426
  by_cases h427 : t ≤ ((299) : ℝ)
  · exact dual_spectral_compact_427 t (le_of_not_ge h426) h427
  by_cases h428 : t ≤ ((300) : ℝ)
  · exact dual_spectral_compact_428 t (le_of_not_ge h427) h428
  · exact dual_spectral_compact_429 t (le_of_not_ge h428) hhi

private theorem dual_spectral_compact_group_430_439 (t : ℝ)
    (hlo : ((301) : ℝ) ≤ t) (hhi : t ≤ ((311) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h430 : t ≤ ((302) : ℝ)
  · exact dual_spectral_compact_430 t hlo h430
  by_cases h431 : t ≤ ((303) : ℝ)
  · exact dual_spectral_compact_431 t (le_of_not_ge h430) h431
  by_cases h432 : t ≤ ((304) : ℝ)
  · exact dual_spectral_compact_432 t (le_of_not_ge h431) h432
  by_cases h433 : t ≤ ((305) : ℝ)
  · exact dual_spectral_compact_433 t (le_of_not_ge h432) h433
  by_cases h434 : t ≤ ((306) : ℝ)
  · exact dual_spectral_compact_434 t (le_of_not_ge h433) h434
  by_cases h435 : t ≤ ((307) : ℝ)
  · exact dual_spectral_compact_435 t (le_of_not_ge h434) h435
  by_cases h436 : t ≤ ((308) : ℝ)
  · exact dual_spectral_compact_436 t (le_of_not_ge h435) h436
  by_cases h437 : t ≤ ((309) : ℝ)
  · exact dual_spectral_compact_437 t (le_of_not_ge h436) h437
  by_cases h438 : t ≤ ((310) : ℝ)
  · exact dual_spectral_compact_438 t (le_of_not_ge h437) h438
  · exact dual_spectral_compact_439 t (le_of_not_ge h438) hhi

private theorem dual_spectral_compact_group_440_449 (t : ℝ)
    (hlo : ((311) : ℝ) ≤ t) (hhi : t ≤ ((321) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h440 : t ≤ ((312) : ℝ)
  · exact dual_spectral_compact_440 t hlo h440
  by_cases h441 : t ≤ ((313) : ℝ)
  · exact dual_spectral_compact_441 t (le_of_not_ge h440) h441
  by_cases h442 : t ≤ ((314) : ℝ)
  · exact dual_spectral_compact_442 t (le_of_not_ge h441) h442
  by_cases h443 : t ≤ ((315) : ℝ)
  · exact dual_spectral_compact_443 t (le_of_not_ge h442) h443
  by_cases h444 : t ≤ ((316) : ℝ)
  · exact dual_spectral_compact_444 t (le_of_not_ge h443) h444
  by_cases h445 : t ≤ ((317) : ℝ)
  · exact dual_spectral_compact_445 t (le_of_not_ge h444) h445
  by_cases h446 : t ≤ ((318) : ℝ)
  · exact dual_spectral_compact_446 t (le_of_not_ge h445) h446
  by_cases h447 : t ≤ ((319) : ℝ)
  · exact dual_spectral_compact_447 t (le_of_not_ge h446) h447
  by_cases h448 : t ≤ ((320) : ℝ)
  · exact dual_spectral_compact_448 t (le_of_not_ge h447) h448
  · exact dual_spectral_compact_449 t (le_of_not_ge h448) hhi

private theorem dual_spectral_compact_group_450_459 (t : ℝ)
    (hlo : ((321) : ℝ) ≤ t) (hhi : t ≤ ((331) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h450 : t ≤ ((322) : ℝ)
  · exact dual_spectral_compact_450 t hlo h450
  by_cases h451 : t ≤ ((323) : ℝ)
  · exact dual_spectral_compact_451 t (le_of_not_ge h450) h451
  by_cases h452 : t ≤ ((324) : ℝ)
  · exact dual_spectral_compact_452 t (le_of_not_ge h451) h452
  by_cases h453 : t ≤ ((325) : ℝ)
  · exact dual_spectral_compact_453 t (le_of_not_ge h452) h453
  by_cases h454 : t ≤ ((326) : ℝ)
  · exact dual_spectral_compact_454 t (le_of_not_ge h453) h454
  by_cases h455 : t ≤ ((327) : ℝ)
  · exact dual_spectral_compact_455 t (le_of_not_ge h454) h455
  by_cases h456 : t ≤ ((328) : ℝ)
  · exact dual_spectral_compact_456 t (le_of_not_ge h455) h456
  by_cases h457 : t ≤ ((329) : ℝ)
  · exact dual_spectral_compact_457 t (le_of_not_ge h456) h457
  by_cases h458 : t ≤ ((330) : ℝ)
  · exact dual_spectral_compact_458 t (le_of_not_ge h457) h458
  · exact dual_spectral_compact_459 t (le_of_not_ge h458) hhi

private theorem dual_spectral_compact_group_460_469 (t : ℝ)
    (hlo : ((331) : ℝ) ≤ t) (hhi : t ≤ ((341) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h460 : t ≤ ((332) : ℝ)
  · exact dual_spectral_compact_460 t hlo h460
  by_cases h461 : t ≤ ((333) : ℝ)
  · exact dual_spectral_compact_461 t (le_of_not_ge h460) h461
  by_cases h462 : t ≤ ((334) : ℝ)
  · exact dual_spectral_compact_462 t (le_of_not_ge h461) h462
  by_cases h463 : t ≤ ((335) : ℝ)
  · exact dual_spectral_compact_463 t (le_of_not_ge h462) h463
  by_cases h464 : t ≤ ((336) : ℝ)
  · exact dual_spectral_compact_464 t (le_of_not_ge h463) h464
  by_cases h465 : t ≤ ((337) : ℝ)
  · exact dual_spectral_compact_465 t (le_of_not_ge h464) h465
  by_cases h466 : t ≤ ((338) : ℝ)
  · exact dual_spectral_compact_466 t (le_of_not_ge h465) h466
  by_cases h467 : t ≤ ((339) : ℝ)
  · exact dual_spectral_compact_467 t (le_of_not_ge h466) h467
  by_cases h468 : t ≤ ((340) : ℝ)
  · exact dual_spectral_compact_468 t (le_of_not_ge h467) h468
  · exact dual_spectral_compact_469 t (le_of_not_ge h468) hhi

private theorem dual_spectral_compact_group_470_479 (t : ℝ)
    (hlo : ((341) : ℝ) ≤ t) (hhi : t ≤ ((351) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h470 : t ≤ ((342) : ℝ)
  · exact dual_spectral_compact_470 t hlo h470
  by_cases h471 : t ≤ ((343) : ℝ)
  · exact dual_spectral_compact_471 t (le_of_not_ge h470) h471
  by_cases h472 : t ≤ ((344) : ℝ)
  · exact dual_spectral_compact_472 t (le_of_not_ge h471) h472
  by_cases h473 : t ≤ ((345) : ℝ)
  · exact dual_spectral_compact_473 t (le_of_not_ge h472) h473
  by_cases h474 : t ≤ ((346) : ℝ)
  · exact dual_spectral_compact_474 t (le_of_not_ge h473) h474
  by_cases h475 : t ≤ ((347) : ℝ)
  · exact dual_spectral_compact_475 t (le_of_not_ge h474) h475
  by_cases h476 : t ≤ ((348) : ℝ)
  · exact dual_spectral_compact_476 t (le_of_not_ge h475) h476
  by_cases h477 : t ≤ ((349) : ℝ)
  · exact dual_spectral_compact_477 t (le_of_not_ge h476) h477
  by_cases h478 : t ≤ ((350) : ℝ)
  · exact dual_spectral_compact_478 t (le_of_not_ge h477) h478
  · exact dual_spectral_compact_479 t (le_of_not_ge h478) hhi

private theorem dual_spectral_compact_group_480_489 (t : ℝ)
    (hlo : ((351) : ℝ) ≤ t) (hhi : t ≤ ((361) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h480 : t ≤ ((352) : ℝ)
  · exact dual_spectral_compact_480 t hlo h480
  by_cases h481 : t ≤ ((353) : ℝ)
  · exact dual_spectral_compact_481 t (le_of_not_ge h480) h481
  by_cases h482 : t ≤ ((354) : ℝ)
  · exact dual_spectral_compact_482 t (le_of_not_ge h481) h482
  by_cases h483 : t ≤ ((355) : ℝ)
  · exact dual_spectral_compact_483 t (le_of_not_ge h482) h483
  by_cases h484 : t ≤ ((356) : ℝ)
  · exact dual_spectral_compact_484 t (le_of_not_ge h483) h484
  by_cases h485 : t ≤ ((357) : ℝ)
  · exact dual_spectral_compact_485 t (le_of_not_ge h484) h485
  by_cases h486 : t ≤ ((358) : ℝ)
  · exact dual_spectral_compact_486 t (le_of_not_ge h485) h486
  by_cases h487 : t ≤ ((359) : ℝ)
  · exact dual_spectral_compact_487 t (le_of_not_ge h486) h487
  by_cases h488 : t ≤ ((360) : ℝ)
  · exact dual_spectral_compact_488 t (le_of_not_ge h487) h488
  · exact dual_spectral_compact_489 t (le_of_not_ge h488) hhi

private theorem dual_spectral_compact_group_490_499 (t : ℝ)
    (hlo : ((361) : ℝ) ≤ t) (hhi : t ≤ ((371) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h490 : t ≤ ((362) : ℝ)
  · exact dual_spectral_compact_490 t hlo h490
  by_cases h491 : t ≤ ((363) : ℝ)
  · exact dual_spectral_compact_491 t (le_of_not_ge h490) h491
  by_cases h492 : t ≤ ((364) : ℝ)
  · exact dual_spectral_compact_492 t (le_of_not_ge h491) h492
  by_cases h493 : t ≤ ((365) : ℝ)
  · exact dual_spectral_compact_493 t (le_of_not_ge h492) h493
  by_cases h494 : t ≤ ((366) : ℝ)
  · exact dual_spectral_compact_494 t (le_of_not_ge h493) h494
  by_cases h495 : t ≤ ((367) : ℝ)
  · exact dual_spectral_compact_495 t (le_of_not_ge h494) h495
  by_cases h496 : t ≤ ((368) : ℝ)
  · exact dual_spectral_compact_496 t (le_of_not_ge h495) h496
  by_cases h497 : t ≤ ((369) : ℝ)
  · exact dual_spectral_compact_497 t (le_of_not_ge h496) h497
  by_cases h498 : t ≤ ((370) : ℝ)
  · exact dual_spectral_compact_498 t (le_of_not_ge h497) h498
  · exact dual_spectral_compact_499 t (le_of_not_ge h498) hhi

private theorem dual_spectral_compact_group_500_509 (t : ℝ)
    (hlo : ((371) : ℝ) ≤ t) (hhi : t ≤ ((381) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h500 : t ≤ ((372) : ℝ)
  · exact dual_spectral_compact_500 t hlo h500
  by_cases h501 : t ≤ ((373) : ℝ)
  · exact dual_spectral_compact_501 t (le_of_not_ge h500) h501
  by_cases h502 : t ≤ ((374) : ℝ)
  · exact dual_spectral_compact_502 t (le_of_not_ge h501) h502
  by_cases h503 : t ≤ ((375) : ℝ)
  · exact dual_spectral_compact_503 t (le_of_not_ge h502) h503
  by_cases h504 : t ≤ ((376) : ℝ)
  · exact dual_spectral_compact_504 t (le_of_not_ge h503) h504
  by_cases h505 : t ≤ ((377) : ℝ)
  · exact dual_spectral_compact_505 t (le_of_not_ge h504) h505
  by_cases h506 : t ≤ ((378) : ℝ)
  · exact dual_spectral_compact_506 t (le_of_not_ge h505) h506
  by_cases h507 : t ≤ ((379) : ℝ)
  · exact dual_spectral_compact_507 t (le_of_not_ge h506) h507
  by_cases h508 : t ≤ ((380) : ℝ)
  · exact dual_spectral_compact_508 t (le_of_not_ge h507) h508
  · exact dual_spectral_compact_509 t (le_of_not_ge h508) hhi

private theorem dual_spectral_compact_group_510_519 (t : ℝ)
    (hlo : ((381) : ℝ) ≤ t) (hhi : t ≤ ((391) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h510 : t ≤ ((382) : ℝ)
  · exact dual_spectral_compact_510 t hlo h510
  by_cases h511 : t ≤ ((383) : ℝ)
  · exact dual_spectral_compact_511 t (le_of_not_ge h510) h511
  by_cases h512 : t ≤ ((384) : ℝ)
  · exact dual_spectral_compact_512 t (le_of_not_ge h511) h512
  by_cases h513 : t ≤ ((385) : ℝ)
  · exact dual_spectral_compact_513 t (le_of_not_ge h512) h513
  by_cases h514 : t ≤ ((386) : ℝ)
  · exact dual_spectral_compact_514 t (le_of_not_ge h513) h514
  by_cases h515 : t ≤ ((387) : ℝ)
  · exact dual_spectral_compact_515 t (le_of_not_ge h514) h515
  by_cases h516 : t ≤ ((388) : ℝ)
  · exact dual_spectral_compact_516 t (le_of_not_ge h515) h516
  by_cases h517 : t ≤ ((389) : ℝ)
  · exact dual_spectral_compact_517 t (le_of_not_ge h516) h517
  by_cases h518 : t ≤ ((390) : ℝ)
  · exact dual_spectral_compact_518 t (le_of_not_ge h517) h518
  · exact dual_spectral_compact_519 t (le_of_not_ge h518) hhi

private theorem dual_spectral_compact_group_520_529 (t : ℝ)
    (hlo : ((391) : ℝ) ≤ t) (hhi : t ≤ ((401) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h520 : t ≤ ((392) : ℝ)
  · exact dual_spectral_compact_520 t hlo h520
  by_cases h521 : t ≤ ((393) : ℝ)
  · exact dual_spectral_compact_521 t (le_of_not_ge h520) h521
  by_cases h522 : t ≤ ((394) : ℝ)
  · exact dual_spectral_compact_522 t (le_of_not_ge h521) h522
  by_cases h523 : t ≤ ((395) : ℝ)
  · exact dual_spectral_compact_523 t (le_of_not_ge h522) h523
  by_cases h524 : t ≤ ((396) : ℝ)
  · exact dual_spectral_compact_524 t (le_of_not_ge h523) h524
  by_cases h525 : t ≤ ((397) : ℝ)
  · exact dual_spectral_compact_525 t (le_of_not_ge h524) h525
  by_cases h526 : t ≤ ((398) : ℝ)
  · exact dual_spectral_compact_526 t (le_of_not_ge h525) h526
  by_cases h527 : t ≤ ((399) : ℝ)
  · exact dual_spectral_compact_527 t (le_of_not_ge h526) h527
  by_cases h528 : t ≤ ((400) : ℝ)
  · exact dual_spectral_compact_528 t (le_of_not_ge h527) h528
  · exact dual_spectral_compact_529 t (le_of_not_ge h528) hhi

private theorem dual_spectral_compact_group_530_539 (t : ℝ)
    (hlo : ((401) : ℝ) ≤ t) (hhi : t ≤ ((411) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h530 : t ≤ ((402) : ℝ)
  · exact dual_spectral_compact_530 t hlo h530
  by_cases h531 : t ≤ ((403) : ℝ)
  · exact dual_spectral_compact_531 t (le_of_not_ge h530) h531
  by_cases h532 : t ≤ ((404) : ℝ)
  · exact dual_spectral_compact_532 t (le_of_not_ge h531) h532
  by_cases h533 : t ≤ ((405) : ℝ)
  · exact dual_spectral_compact_533 t (le_of_not_ge h532) h533
  by_cases h534 : t ≤ ((406) : ℝ)
  · exact dual_spectral_compact_534 t (le_of_not_ge h533) h534
  by_cases h535 : t ≤ ((407) : ℝ)
  · exact dual_spectral_compact_535 t (le_of_not_ge h534) h535
  by_cases h536 : t ≤ ((408) : ℝ)
  · exact dual_spectral_compact_536 t (le_of_not_ge h535) h536
  by_cases h537 : t ≤ ((409) : ℝ)
  · exact dual_spectral_compact_537 t (le_of_not_ge h536) h537
  by_cases h538 : t ≤ ((410) : ℝ)
  · exact dual_spectral_compact_538 t (le_of_not_ge h537) h538
  · exact dual_spectral_compact_539 t (le_of_not_ge h538) hhi

private theorem dual_spectral_compact_group_540_549 (t : ℝ)
    (hlo : ((411) : ℝ) ≤ t) (hhi : t ≤ ((421) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h540 : t ≤ ((412) : ℝ)
  · exact dual_spectral_compact_540 t hlo h540
  by_cases h541 : t ≤ ((413) : ℝ)
  · exact dual_spectral_compact_541 t (le_of_not_ge h540) h541
  by_cases h542 : t ≤ ((414) : ℝ)
  · exact dual_spectral_compact_542 t (le_of_not_ge h541) h542
  by_cases h543 : t ≤ ((415) : ℝ)
  · exact dual_spectral_compact_543 t (le_of_not_ge h542) h543
  by_cases h544 : t ≤ ((416) : ℝ)
  · exact dual_spectral_compact_544 t (le_of_not_ge h543) h544
  by_cases h545 : t ≤ ((417) : ℝ)
  · exact dual_spectral_compact_545 t (le_of_not_ge h544) h545
  by_cases h546 : t ≤ ((418) : ℝ)
  · exact dual_spectral_compact_546 t (le_of_not_ge h545) h546
  by_cases h547 : t ≤ ((419) : ℝ)
  · exact dual_spectral_compact_547 t (le_of_not_ge h546) h547
  by_cases h548 : t ≤ ((420) : ℝ)
  · exact dual_spectral_compact_548 t (le_of_not_ge h547) h548
  · exact dual_spectral_compact_549 t (le_of_not_ge h548) hhi

private theorem dual_spectral_compact_group_550_559 (t : ℝ)
    (hlo : ((421) : ℝ) ≤ t) (hhi : t ≤ ((431) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h550 : t ≤ ((422) : ℝ)
  · exact dual_spectral_compact_550 t hlo h550
  by_cases h551 : t ≤ ((423) : ℝ)
  · exact dual_spectral_compact_551 t (le_of_not_ge h550) h551
  by_cases h552 : t ≤ ((424) : ℝ)
  · exact dual_spectral_compact_552 t (le_of_not_ge h551) h552
  by_cases h553 : t ≤ ((425) : ℝ)
  · exact dual_spectral_compact_553 t (le_of_not_ge h552) h553
  by_cases h554 : t ≤ ((426) : ℝ)
  · exact dual_spectral_compact_554 t (le_of_not_ge h553) h554
  by_cases h555 : t ≤ ((427) : ℝ)
  · exact dual_spectral_compact_555 t (le_of_not_ge h554) h555
  by_cases h556 : t ≤ ((428) : ℝ)
  · exact dual_spectral_compact_556 t (le_of_not_ge h555) h556
  by_cases h557 : t ≤ ((429) : ℝ)
  · exact dual_spectral_compact_557 t (le_of_not_ge h556) h557
  by_cases h558 : t ≤ ((430) : ℝ)
  · exact dual_spectral_compact_558 t (le_of_not_ge h557) h558
  · exact dual_spectral_compact_559 t (le_of_not_ge h558) hhi

private theorem dual_spectral_compact_group_560_569 (t : ℝ)
    (hlo : ((431) : ℝ) ≤ t) (hhi : t ≤ ((441) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h560 : t ≤ ((432) : ℝ)
  · exact dual_spectral_compact_560 t hlo h560
  by_cases h561 : t ≤ ((433) : ℝ)
  · exact dual_spectral_compact_561 t (le_of_not_ge h560) h561
  by_cases h562 : t ≤ ((434) : ℝ)
  · exact dual_spectral_compact_562 t (le_of_not_ge h561) h562
  by_cases h563 : t ≤ ((435) : ℝ)
  · exact dual_spectral_compact_563 t (le_of_not_ge h562) h563
  by_cases h564 : t ≤ ((436) : ℝ)
  · exact dual_spectral_compact_564 t (le_of_not_ge h563) h564
  by_cases h565 : t ≤ ((437) : ℝ)
  · exact dual_spectral_compact_565 t (le_of_not_ge h564) h565
  by_cases h566 : t ≤ ((438) : ℝ)
  · exact dual_spectral_compact_566 t (le_of_not_ge h565) h566
  by_cases h567 : t ≤ ((439) : ℝ)
  · exact dual_spectral_compact_567 t (le_of_not_ge h566) h567
  by_cases h568 : t ≤ ((440) : ℝ)
  · exact dual_spectral_compact_568 t (le_of_not_ge h567) h568
  · exact dual_spectral_compact_569 t (le_of_not_ge h568) hhi

private theorem dual_spectral_compact_group_570_579 (t : ℝ)
    (hlo : ((441) : ℝ) ≤ t) (hhi : t ≤ ((451) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h570 : t ≤ ((442) : ℝ)
  · exact dual_spectral_compact_570 t hlo h570
  by_cases h571 : t ≤ ((443) : ℝ)
  · exact dual_spectral_compact_571 t (le_of_not_ge h570) h571
  by_cases h572 : t ≤ ((444) : ℝ)
  · exact dual_spectral_compact_572 t (le_of_not_ge h571) h572
  by_cases h573 : t ≤ ((445) : ℝ)
  · exact dual_spectral_compact_573 t (le_of_not_ge h572) h573
  by_cases h574 : t ≤ ((446) : ℝ)
  · exact dual_spectral_compact_574 t (le_of_not_ge h573) h574
  by_cases h575 : t ≤ ((447) : ℝ)
  · exact dual_spectral_compact_575 t (le_of_not_ge h574) h575
  by_cases h576 : t ≤ ((448) : ℝ)
  · exact dual_spectral_compact_576 t (le_of_not_ge h575) h576
  by_cases h577 : t ≤ ((449) : ℝ)
  · exact dual_spectral_compact_577 t (le_of_not_ge h576) h577
  by_cases h578 : t ≤ ((450) : ℝ)
  · exact dual_spectral_compact_578 t (le_of_not_ge h577) h578
  · exact dual_spectral_compact_579 t (le_of_not_ge h578) hhi

private theorem dual_spectral_compact_group_580_589 (t : ℝ)
    (hlo : ((451) : ℝ) ≤ t) (hhi : t ≤ ((461) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h580 : t ≤ ((452) : ℝ)
  · exact dual_spectral_compact_580 t hlo h580
  by_cases h581 : t ≤ ((453) : ℝ)
  · exact dual_spectral_compact_581 t (le_of_not_ge h580) h581
  by_cases h582 : t ≤ ((454) : ℝ)
  · exact dual_spectral_compact_582 t (le_of_not_ge h581) h582
  by_cases h583 : t ≤ ((455) : ℝ)
  · exact dual_spectral_compact_583 t (le_of_not_ge h582) h583
  by_cases h584 : t ≤ ((456) : ℝ)
  · exact dual_spectral_compact_584 t (le_of_not_ge h583) h584
  by_cases h585 : t ≤ ((457) : ℝ)
  · exact dual_spectral_compact_585 t (le_of_not_ge h584) h585
  by_cases h586 : t ≤ ((458) : ℝ)
  · exact dual_spectral_compact_586 t (le_of_not_ge h585) h586
  by_cases h587 : t ≤ ((459) : ℝ)
  · exact dual_spectral_compact_587 t (le_of_not_ge h586) h587
  by_cases h588 : t ≤ ((460) : ℝ)
  · exact dual_spectral_compact_588 t (le_of_not_ge h587) h588
  · exact dual_spectral_compact_589 t (le_of_not_ge h588) hhi

private theorem dual_spectral_compact_group_590_599 (t : ℝ)
    (hlo : ((461) : ℝ) ≤ t) (hhi : t ≤ ((471) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h590 : t ≤ ((462) : ℝ)
  · exact dual_spectral_compact_590 t hlo h590
  by_cases h591 : t ≤ ((463) : ℝ)
  · exact dual_spectral_compact_591 t (le_of_not_ge h590) h591
  by_cases h592 : t ≤ ((464) : ℝ)
  · exact dual_spectral_compact_592 t (le_of_not_ge h591) h592
  by_cases h593 : t ≤ ((465) : ℝ)
  · exact dual_spectral_compact_593 t (le_of_not_ge h592) h593
  by_cases h594 : t ≤ ((466) : ℝ)
  · exact dual_spectral_compact_594 t (le_of_not_ge h593) h594
  by_cases h595 : t ≤ ((467) : ℝ)
  · exact dual_spectral_compact_595 t (le_of_not_ge h594) h595
  by_cases h596 : t ≤ ((468) : ℝ)
  · exact dual_spectral_compact_596 t (le_of_not_ge h595) h596
  by_cases h597 : t ≤ ((469) : ℝ)
  · exact dual_spectral_compact_597 t (le_of_not_ge h596) h597
  by_cases h598 : t ≤ ((470) : ℝ)
  · exact dual_spectral_compact_598 t (le_of_not_ge h597) h598
  · exact dual_spectral_compact_599 t (le_of_not_ge h598) hhi

private theorem dual_spectral_compact_group_600_609 (t : ℝ)
    (hlo : ((471) : ℝ) ≤ t) (hhi : t ≤ ((481) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h600 : t ≤ ((472) : ℝ)
  · exact dual_spectral_compact_600 t hlo h600
  by_cases h601 : t ≤ ((473) : ℝ)
  · exact dual_spectral_compact_601 t (le_of_not_ge h600) h601
  by_cases h602 : t ≤ ((474) : ℝ)
  · exact dual_spectral_compact_602 t (le_of_not_ge h601) h602
  by_cases h603 : t ≤ ((475) : ℝ)
  · exact dual_spectral_compact_603 t (le_of_not_ge h602) h603
  by_cases h604 : t ≤ ((476) : ℝ)
  · exact dual_spectral_compact_604 t (le_of_not_ge h603) h604
  by_cases h605 : t ≤ ((477) : ℝ)
  · exact dual_spectral_compact_605 t (le_of_not_ge h604) h605
  by_cases h606 : t ≤ ((478) : ℝ)
  · exact dual_spectral_compact_606 t (le_of_not_ge h605) h606
  by_cases h607 : t ≤ ((479) : ℝ)
  · exact dual_spectral_compact_607 t (le_of_not_ge h606) h607
  by_cases h608 : t ≤ ((480) : ℝ)
  · exact dual_spectral_compact_608 t (le_of_not_ge h607) h608
  · exact dual_spectral_compact_609 t (le_of_not_ge h608) hhi

private theorem dual_spectral_compact_group_610_619 (t : ℝ)
    (hlo : ((481) : ℝ) ≤ t) (hhi : t ≤ ((491) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h610 : t ≤ ((482) : ℝ)
  · exact dual_spectral_compact_610 t hlo h610
  by_cases h611 : t ≤ ((483) : ℝ)
  · exact dual_spectral_compact_611 t (le_of_not_ge h610) h611
  by_cases h612 : t ≤ ((484) : ℝ)
  · exact dual_spectral_compact_612 t (le_of_not_ge h611) h612
  by_cases h613 : t ≤ ((485) : ℝ)
  · exact dual_spectral_compact_613 t (le_of_not_ge h612) h613
  by_cases h614 : t ≤ ((486) : ℝ)
  · exact dual_spectral_compact_614 t (le_of_not_ge h613) h614
  by_cases h615 : t ≤ ((487) : ℝ)
  · exact dual_spectral_compact_615 t (le_of_not_ge h614) h615
  by_cases h616 : t ≤ ((488) : ℝ)
  · exact dual_spectral_compact_616 t (le_of_not_ge h615) h616
  by_cases h617 : t ≤ ((489) : ℝ)
  · exact dual_spectral_compact_617 t (le_of_not_ge h616) h617
  by_cases h618 : t ≤ ((490) : ℝ)
  · exact dual_spectral_compact_618 t (le_of_not_ge h617) h618
  · exact dual_spectral_compact_619 t (le_of_not_ge h618) hhi

private theorem dual_spectral_compact_group_620_628 (t : ℝ)
    (hlo : ((491) : ℝ) ≤ t) (hhi : t ≤ ((500) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases h620 : t ≤ ((492) : ℝ)
  · exact dual_spectral_compact_620 t hlo h620
  by_cases h621 : t ≤ ((493) : ℝ)
  · exact dual_spectral_compact_621 t (le_of_not_ge h620) h621
  by_cases h622 : t ≤ ((494) : ℝ)
  · exact dual_spectral_compact_622 t (le_of_not_ge h621) h622
  by_cases h623 : t ≤ ((495) : ℝ)
  · exact dual_spectral_compact_623 t (le_of_not_ge h622) h623
  by_cases h624 : t ≤ ((496) : ℝ)
  · exact dual_spectral_compact_624 t (le_of_not_ge h623) h624
  by_cases h625 : t ≤ ((497) : ℝ)
  · exact dual_spectral_compact_625 t (le_of_not_ge h624) h625
  by_cases h626 : t ≤ ((498) : ℝ)
  · exact dual_spectral_compact_626 t (le_of_not_ge h625) h626
  by_cases h627 : t ≤ ((499) : ℝ)
  · exact dual_spectral_compact_627 t (le_of_not_ge h626) h627
  · exact dual_spectral_compact_628 t (le_of_not_ge h627) hhi

private theorem dual_spectral_compact_super_000_099 (t : ℝ)
    (hlo : ((0) : ℝ) ≤ t) (hhi : t ≤ ((117 / 4) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg00 : t ≤ ((13 / 4) : ℝ)
  · exact dual_spectral_compact_group_000_009 t hlo hg00
  by_cases hg01 : t ≤ ((9 / 2) : ℝ)
  · exact dual_spectral_compact_group_010_019 t (le_of_not_ge hg00) hg01
  by_cases hg02 : t ≤ ((51 / 8) : ℝ)
  · exact dual_spectral_compact_group_020_029 t (le_of_not_ge hg01) hg02
  by_cases hg03 : t ≤ ((81 / 8) : ℝ)
  · exact dual_spectral_compact_group_030_039 t (le_of_not_ge hg02) hg03
  by_cases hg04 : t ≤ ((23 / 2) : ℝ)
  · exact dual_spectral_compact_group_040_049 t (le_of_not_ge hg03) hg04
  by_cases hg05 : t ≤ ((539 / 32) : ℝ)
  · exact dual_spectral_compact_group_050_059 t (le_of_not_ge hg04) hg05
  by_cases hg06 : t ≤ ((20) : ℝ)
  · exact dual_spectral_compact_group_060_069 t (le_of_not_ge hg05) hg06
  by_cases hg07 : t ≤ ((187 / 8) : ℝ)
  · exact dual_spectral_compact_group_070_079 t (le_of_not_ge hg06) hg07
  by_cases hg08 : t ≤ ((28) : ℝ)
  · exact dual_spectral_compact_group_080_089 t (le_of_not_ge hg07) hg08
  · exact dual_spectral_compact_group_090_099 t (le_of_not_ge hg08) hhi

private theorem dual_spectral_compact_super_100_199 (t : ℝ)
    (hlo : ((117 / 4) : ℝ) ≤ t) (hhi : t ≤ ((183 / 2) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg10 : t ≤ ((69 / 2) : ℝ)
  · exact dual_spectral_compact_group_100_109 t hlo hg10
  by_cases hg11 : t ≤ ((73 / 2) : ℝ)
  · exact dual_spectral_compact_group_110_119 t (le_of_not_ge hg10) hg11
  by_cases hg12 : t ≤ ((41) : ℝ)
  · exact dual_spectral_compact_group_120_129 t (le_of_not_ge hg11) hg12
  by_cases hg13 : t ≤ ((48) : ℝ)
  · exact dual_spectral_compact_group_130_139 t (le_of_not_ge hg12) hg13
  by_cases hg14 : t ≤ ((55) : ℝ)
  · exact dual_spectral_compact_group_140_149 t (le_of_not_ge hg13) hg14
  by_cases hg15 : t ≤ ((62) : ℝ)
  · exact dual_spectral_compact_group_150_159 t (le_of_not_ge hg14) hg15
  by_cases hg16 : t ≤ ((541 / 8) : ℝ)
  · exact dual_spectral_compact_group_160_169 t (le_of_not_ge hg15) hg16
  by_cases hg17 : t ≤ ((74) : ℝ)
  · exact dual_spectral_compact_group_170_179 t (le_of_not_ge hg16) hg17
  by_cases hg18 : t ≤ ((82) : ℝ)
  · exact dual_spectral_compact_group_180_189 t (le_of_not_ge hg17) hg18
  · exact dual_spectral_compact_group_190_199 t (le_of_not_ge hg18) hhi

private theorem dual_spectral_compact_super_200_299 (t : ℝ)
    (hlo : ((183 / 2) : ℝ) ≤ t) (hhi : t ≤ ((173) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg20 : t ≤ ((741 / 8) : ℝ)
  · exact dual_spectral_compact_group_200_209 t hlo hg20
  by_cases hg21 : t ≤ ((99) : ℝ)
  · exact dual_spectral_compact_group_210_219 t (le_of_not_ge hg20) hg21
  by_cases hg22 : t ≤ ((107) : ℝ)
  · exact dual_spectral_compact_group_220_229 t (le_of_not_ge hg21) hg22
  by_cases hg23 : t ≤ ((233 / 2) : ℝ)
  · exact dual_spectral_compact_group_230_239 t (le_of_not_ge hg22) hg23
  by_cases hg24 : t ≤ ((125) : ℝ)
  · exact dual_spectral_compact_group_240_249 t (le_of_not_ge hg23) hg24
  by_cases hg25 : t ≤ ((135) : ℝ)
  · exact dual_spectral_compact_group_250_259 t (le_of_not_ge hg24) hg25
  by_cases hg26 : t ≤ ((144) : ℝ)
  · exact dual_spectral_compact_group_260_269 t (le_of_not_ge hg25) hg26
  by_cases hg27 : t ≤ ((154) : ℝ)
  · exact dual_spectral_compact_group_270_279 t (le_of_not_ge hg26) hg27
  by_cases hg28 : t ≤ ((164) : ℝ)
  · exact dual_spectral_compact_group_280_289 t (le_of_not_ge hg27) hg28
  · exact dual_spectral_compact_group_290_299 t (le_of_not_ge hg28) hhi

private theorem dual_spectral_compact_super_300_399 (t : ℝ)
    (hlo : ((173) : ℝ) ≤ t) (hhi : t ≤ ((271) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg30 : t ≤ ((183) : ℝ)
  · exact dual_spectral_compact_group_300_309 t hlo hg30
  by_cases hg31 : t ≤ ((192) : ℝ)
  · exact dual_spectral_compact_group_310_319 t (le_of_not_ge hg30) hg31
  by_cases hg32 : t ≤ ((202) : ℝ)
  · exact dual_spectral_compact_group_320_329 t (le_of_not_ge hg31) hg32
  by_cases hg33 : t ≤ ((212) : ℝ)
  · exact dual_spectral_compact_group_330_339 t (le_of_not_ge hg32) hg33
  by_cases hg34 : t ≤ ((221) : ℝ)
  · exact dual_spectral_compact_group_340_349 t (le_of_not_ge hg33) hg34
  by_cases hg35 : t ≤ ((231) : ℝ)
  · exact dual_spectral_compact_group_350_359 t (le_of_not_ge hg34) hg35
  by_cases hg36 : t ≤ ((241) : ℝ)
  · exact dual_spectral_compact_group_360_369 t (le_of_not_ge hg35) hg36
  by_cases hg37 : t ≤ ((251) : ℝ)
  · exact dual_spectral_compact_group_370_379 t (le_of_not_ge hg36) hg37
  by_cases hg38 : t ≤ ((261) : ℝ)
  · exact dual_spectral_compact_group_380_389 t (le_of_not_ge hg37) hg38
  · exact dual_spectral_compact_group_390_399 t (le_of_not_ge hg38) hhi

private theorem dual_spectral_compact_super_400_499 (t : ℝ)
    (hlo : ((271) : ℝ) ≤ t) (hhi : t ≤ ((371) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg40 : t ≤ ((281) : ℝ)
  · exact dual_spectral_compact_group_400_409 t hlo hg40
  by_cases hg41 : t ≤ ((291) : ℝ)
  · exact dual_spectral_compact_group_410_419 t (le_of_not_ge hg40) hg41
  by_cases hg42 : t ≤ ((301) : ℝ)
  · exact dual_spectral_compact_group_420_429 t (le_of_not_ge hg41) hg42
  by_cases hg43 : t ≤ ((311) : ℝ)
  · exact dual_spectral_compact_group_430_439 t (le_of_not_ge hg42) hg43
  by_cases hg44 : t ≤ ((321) : ℝ)
  · exact dual_spectral_compact_group_440_449 t (le_of_not_ge hg43) hg44
  by_cases hg45 : t ≤ ((331) : ℝ)
  · exact dual_spectral_compact_group_450_459 t (le_of_not_ge hg44) hg45
  by_cases hg46 : t ≤ ((341) : ℝ)
  · exact dual_spectral_compact_group_460_469 t (le_of_not_ge hg45) hg46
  by_cases hg47 : t ≤ ((351) : ℝ)
  · exact dual_spectral_compact_group_470_479 t (le_of_not_ge hg46) hg47
  by_cases hg48 : t ≤ ((361) : ℝ)
  · exact dual_spectral_compact_group_480_489 t (le_of_not_ge hg47) hg48
  · exact dual_spectral_compact_group_490_499 t (le_of_not_ge hg48) hhi

private theorem dual_spectral_compact_super_500_599 (t : ℝ)
    (hlo : ((371) : ℝ) ≤ t) (hhi : t ≤ ((471) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg50 : t ≤ ((381) : ℝ)
  · exact dual_spectral_compact_group_500_509 t hlo hg50
  by_cases hg51 : t ≤ ((391) : ℝ)
  · exact dual_spectral_compact_group_510_519 t (le_of_not_ge hg50) hg51
  by_cases hg52 : t ≤ ((401) : ℝ)
  · exact dual_spectral_compact_group_520_529 t (le_of_not_ge hg51) hg52
  by_cases hg53 : t ≤ ((411) : ℝ)
  · exact dual_spectral_compact_group_530_539 t (le_of_not_ge hg52) hg53
  by_cases hg54 : t ≤ ((421) : ℝ)
  · exact dual_spectral_compact_group_540_549 t (le_of_not_ge hg53) hg54
  by_cases hg55 : t ≤ ((431) : ℝ)
  · exact dual_spectral_compact_group_550_559 t (le_of_not_ge hg54) hg55
  by_cases hg56 : t ≤ ((441) : ℝ)
  · exact dual_spectral_compact_group_560_569 t (le_of_not_ge hg55) hg56
  by_cases hg57 : t ≤ ((451) : ℝ)
  · exact dual_spectral_compact_group_570_579 t (le_of_not_ge hg56) hg57
  by_cases hg58 : t ≤ ((461) : ℝ)
  · exact dual_spectral_compact_group_580_589 t (le_of_not_ge hg57) hg58
  · exact dual_spectral_compact_group_590_599 t (le_of_not_ge hg58) hhi

private theorem dual_spectral_compact_super_600_628 (t : ℝ)
    (hlo : ((471) : ℝ) ≤ t) (hhi : t ≤ ((500) : ℝ)) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hg60 : t ≤ ((481) : ℝ)
  · exact dual_spectral_compact_group_600_609 t hlo hg60
  by_cases hg61 : t ≤ ((491) : ℝ)
  · exact dual_spectral_compact_group_610_619 t (le_of_not_ge hg60) hg61
  · exact dual_spectral_compact_group_620_628 t (le_of_not_ge hg61) hhi

private theorem dual_spectral_compact (t : ℝ) (ht : 0 ≤ t) (h500 : t ≤ 500) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases hs0 : t ≤ ((117 / 4) : ℝ)
  · exact dual_spectral_compact_super_000_099 t ht hs0
  by_cases hs1 : t ≤ ((183 / 2) : ℝ)
  · exact dual_spectral_compact_super_100_199 t (le_of_not_ge hs0) hs1
  by_cases hs2 : t ≤ ((173) : ℝ)
  · exact dual_spectral_compact_super_200_299 t (le_of_not_ge hs1) hs2
  by_cases hs3 : t ≤ ((271) : ℝ)
  · exact dual_spectral_compact_super_300_399 t (le_of_not_ge hs2) hs3
  by_cases hs4 : t ≤ ((371) : ℝ)
  · exact dual_spectral_compact_super_400_499 t (le_of_not_ge hs3) hs4
  by_cases hs5 : t ≤ ((471) : ℝ)
  · exact dual_spectral_compact_super_500_599 t (le_of_not_ge hs4) hs5
  · exact dual_spectral_compact_super_600_628 t (le_of_not_ge hs5) h500

/-- The exact compact cover and the Sonin tail together certify the dual spectral
inequality on the whole nonnegative half-line. -/
theorem dual_spectral_nonnegative (t : ℝ) (ht : 0 ≤ t) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t := by
  by_cases htail : 500 ≤ t
  · exact dual_spectral_tail htail
  · exact dual_spectral_compact t ht (le_of_not_ge htail)

end Erdos232
