/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.HunterShellLabeling

/-!
# From orbit differences to red points in long progressions

The Fourier argument supplies `i alpha - j alpha`.  Shifting its target by
`(L-1) alpha` turns this signed difference into the genuine progression
index `L-1+i-j`, which lies in `[0,2L-2]`.  This file also partitions every
short Euclidean displacement into a radial shell and applies the random
labeling lemma to all encoded progressions at once.
-/

namespace Erdos721.HunterProgressions

open Function Set
open scoped ENNReal BigOperators

open HunterTorus HunterAnnulus HunterCenters HunterDistributedCenters
  HunterSeparatedCenters HunterDiophantine HunterFourierCutoff
  HunterOrbitCenters HunterColoring HunterShellLabeling

/-- Every vector below the outer endpoint `K*q` belongs to one of the first
`K` half-open radial shells. -/
lemma exists_mem_shell_of_norm_lt_mul {D K : ℕ} {q : ℝ}
    (hq : 0 < q) {v : EuclideanSpace ℝ (Fin D)}
    (hv : ‖v‖ < (K : ℝ) * q) :
    ∃ k : Fin K, v ∈ shell q k.val := by
  let n : ℕ := ⌊‖v‖ / q⌋₊
  have hratio0 : 0 ≤ ‖v‖ / q := div_nonneg (norm_nonneg _) hq.le
  have hnle : (n : ℝ) ≤ ‖v‖ / q := by
    simpa only [n] using Nat.floor_le hratio0
  have hlt : ‖v‖ / q < (n : ℝ) + 1 := by
    simpa only [n] using Nat.lt_floor_add_one (‖v‖ / q)
  have hratioK : ‖v‖ / q < K := by
    rw [div_lt_iff₀ hq]
    exact hv
  have hnK : n < K := by
    exact_mod_cast hnle.trans_lt hratioK
  refine ⟨⟨n, hnK⟩, ?_, ?_⟩
  · rw [le_div_iff₀ hq] at hnle
    simpa [n] using hnle
  · rw [div_lt_iff₀ hq] at hlt
    norm_num at hlt ⊢
    simpa [n, add_mul] using hlt

/-- Projection followed by the centered lift is exact for vectors strictly
shorter than half a torus period. -/
lemma centeredLift_project_eq_of_norm_lt_half {D : ℕ}
    {v : EuclideanSpace ℝ (Fin D)} (hv : ‖v‖ < 1 / 2) :
    centeredLift (project v) = v := by
  apply centeredLift_project
  intro i
  have hi : |v i| < 1 / 2 :=
    (HunterColoring.abs_apply_le_norm v i).trans_lt hv
  rw [abs_lt] at hi
  exact ⟨hi.1.le, hi.2⟩

lemma nsmul_nsmul_comm {D : ℕ} (theta : Torus D) (m n : ℕ) :
    m • (n • theta) = (m * n) • theta := by
  rw [Nat.mul_comm, mul_nsmul]

/-- One encoded progression and one center block produce a shell-matched
actual progression term. -/
theorem exists_shell_orbit_term
    {D H R Y S K N L : ℕ}
    {phaseRadius cutoffRadius massBound epsilon q error : ℝ}
    {theta : Torus D} {x : CenterFamily Y S D}
    (hdist : PhaseDistributed (H := H) (R := R) phaseRadius x)
    (hres : LowResonanceRank (H := H) (R := R) N epsilon theta)
    (F : FourierCutoff D H cutoffRadius massBound)
    (hcutoffRadius : 0 ≤ cutoffRadius) (hepsilon : 0 < epsilon)
    (hlarge : massBound * (2 * epsilon)⁻¹ ^ 2 < (L : ℝ) ^ 2)
    (hq : 0 < q)
    (herror : 2 * Real.sqrt R * phaseRadius +
      Real.sqrt D * cutoffRadius ≤ error)
    (herrorShell : error < (K : ℝ) * q)
    (herrorHalf : error < 1 / 2)
    (hL : 0 < L) (r : Fin N × Fin N) (b : Fin Y) :
    ∃ s : Fin S, ∃ k : Fin K, ∃ ell : ℕ,
      ell < 2 * L - 1 ∧
      centeredLift
          ((r.1.val + ell * (r.2.val + 1)) • theta - x b s) ∈
        shell q k.val := by
  let d : ℕ := r.2.val + 1
  let alpha : Torus D := d • theta
  have hrank : Module.finrank ℚ
      (resonanceSubspace (H := H) epsilon alpha) < R := by
    simpa only [alpha, d] using
      finrank_resonanceSubspace_lt hres r.2
  let xStar : Torus D := r.1.val • theta + (L - 1) • alpha
  obtain ⟨s, i, j, w, hw, hhit⟩ :=
    exists_orbit_hit_center hdist hrank F hcutoffRadius hepsilon hlarge b xStar
  have hjle : j.val ≤ (L - 1) + i.val := by omega
  let ell : ℕ := (L - 1 + i.val) - j.val
  have helladd : ell + j.val = L - 1 + i.val := by
    exact Nat.sub_add_cancel hjle
  have helllt : ell < 2 * L - 1 := by
    dsimp only [ell]
    omega
  have halpha :
      ell • alpha + j.val • alpha =
        (L - 1) • alpha + i.val • alpha := by
    rw [← add_nsmul, helladd, add_nsmul]
  have hindex :
      i.val • alpha - j.val • alpha + xStar =
        (r.1.val + ell * d) • theta := by
    calc
      _ = r.1.val • theta +
          ((L - 1) • alpha + i.val • alpha) - j.val • alpha := by
        dsimp only [xStar]
        abel
      _ = r.1.val • theta +
          (ell • alpha + j.val • alpha) - j.val • alpha := by
        rw [halpha]
      _ = r.1.val • theta + ell • alpha := by abel
      _ = (r.1.val + ell * d) • theta := by
        rw [add_nsmul, nsmul_nsmul_comm]
  have hterm : (r.1.val + ell * d) • theta = x b s + project w := by
    rw [← hindex]
    exact hhit
  have hdiff :
      (r.1.val + ell * d) • theta - x b s = project w := by
    rw [hterm]
    abel
  have hwerror : ‖w‖ ≤ error := hw.trans herror
  obtain ⟨k, hk⟩ := exists_mem_shell_of_norm_lt_mul hq
    (hwerror.trans_lt herrorShell)
  refine ⟨s, k, ell, helllt, ?_⟩
  rw [show r.2.val + 1 = d by rfl, hdiff,
    centeredLift_project_eq_of_norm_lt_half
      (hwerror.trans_lt herrorHalf)]
  exact hk

/-- Encoded starts and positive steps used in the finite labeling union
bound.  Invalid pairs are harmless; valid progressions form a subset. -/
abbrev ProgressionRequest (N : ℕ) := Fin N × Fin N

/-- Once every encoded progression has one shell candidate in each block,
the labeling union bound gives a red point in every valid progression of
length `2L-1`. -/
theorem exists_labeling_hitsEveryAP
    {D H R Y S K N L : ℕ}
    {phaseRadius cutoffRadius massBound epsilon q error : ℝ}
    {theta : Torus D} {x : CenterFamily Y S D}
    (hdist : PhaseDistributed (H := H) (R := R) phaseRadius x)
    (hres : LowResonanceRank (H := H) (R := R) N epsilon theta)
    (F : FourierCutoff D H cutoffRadius massBound)
    (hcutoffRadius : 0 ≤ cutoffRadius) (hepsilon : 0 < epsilon)
    (hlarge : massBound * (2 * epsilon)⁻¹ ^ 2 < (L : ℝ) ^ 2)
    (hq : 0 < q)
    (herror : 2 * Real.sqrt R * phaseRadius +
      Real.sqrt D * cutoffRadius ≤ error)
    (herrorShell : error < (K : ℝ) * q)
    (herrorHalf : error < 1 / 2)
    (hL : 2 ≤ L)
    (hK : 0 < K)
    (hlabelSmall : (N ^ 2 : ℕ) *
      (1 - (K : ℝ≥0∞)⁻¹) ^ Y < 1) :
    ∃ label : ShellLabeling Y S K,
      HitsEveryAP N (2 * L - 1) (IsHunterRed q theta x label) := by
  have hcandidate : ∀ r : ProgressionRequest N, ∀ b : Fin Y,
      ∃ s : Fin S, ∃ k : Fin K, ∃ ell : ℕ,
        ell < 2 * L - 1 ∧
        centeredLift
            ((r.1.val + ell * (r.2.val + 1)) • theta - x b s) ∈
          shell q k.val :=
    exists_shell_orbit_term hdist hres F hcutoffRadius hepsilon hlarge hq
      herror herrorShell herrorHalf (by omega)
  choose chosen wanted offset hoffset hshell using hcandidate
  have hcard : Fintype.card (ProgressionRequest N) = N ^ 2 := by
    simp [ProgressionRequest, pow_two]
  obtain ⟨label, hlabel⟩ := exists_shellLabeling hK chosen wanted (by
    rw [hcard]
    exact hlabelSmall)
  refine ⟨label, ?_⟩
  intro a d hd hbound
  have haN : a < N := by omega
  have hdN : d < N := by
    have hcoeff : 1 ≤ 2 * L - 1 - 1 := by omega
    nlinarith
  let r : ProgressionRequest N :=
    (⟨a, haN⟩, ⟨d - 1, by omega⟩)
  obtain ⟨b, hb⟩ := hlabel r
  let ell := offset r b
  refine ⟨⟨ell, hoffset r b⟩, ?_⟩
  refine ⟨(b, chosen r b), ?_⟩
  have hdcode : r.2.val + 1 = d := by
    dsimp only [r]
    omega
  have hastart : r.1.val = a := rfl
  rw [hb]
  simpa only [hastart, hdcode, ell, centerAt] using hshell r b

end Erdos721.HunterProgressions
