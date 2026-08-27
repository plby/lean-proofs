/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceBadPinnedCount

/-! # A single residue assignment satisfying all four source count estimates -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

open scoped Classical in
theorem finite_exists_avoid_events {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : Ω → ℝ) (E : I → Ω → Prop) (hμ : ∀ b, 0 ≤ μ b) (hsum : ∑ b, μ b = 1)
    (hbad : (∑ i, ∑ b, if E i b then μ b else 0) < 1) : ∃ b, ∀ i, ¬E i b := by
  classical
  by_contra hn
  push Not at hn
  have hpoint (b : Ω) : μ b ≤ ∑ i, if E i b then μ b else 0 := by
    obtain ⟨i, hi⟩ := hn b
    have hnonneg (j : I) : 0 ≤ (if E j b then μ b else 0) := by
      split_ifs
      · exact hμ b
      · exact le_rfl
    have hle := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : I => if E j b then μ b else 0) (a := i)
      (fun j _hj => hnonneg j) (Finset.mem_univ i)
    simpa only [if_pos hi] using hle
  have hcover : 1 ≤ ∑ i, ∑ b, if E i b then μ b else 0 := by
    calc
      1 = ∑ b, μ b := hsum.symm
      _ ≤ ∑ b, ∑ i, if E i b then μ b else 0 := Finset.sum_le_sum fun b _hb => hpoint b
      _ = _ := Finset.sum_comm
  linarith

theorem eventually_exists_source_good_assignment {a c e : ℝ}
    (ha : 0 < a) (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∃ b : ResidueAssignment (sourceSmallPrimes a x),
        |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x| <
            sourceSurvivorMean a c x / Real.log (Real.log (x : ℝ)) ∧
        ((D.badTuplePrimes (sourceSmallPrimes a x) b).card : ℝ) <
            4 * (x : ℝ) / Real.log (x : ℝ) ^ 4 ∧
        ((D.badPinnedVertices (sourceSmallPrimes a x) b).card : ℝ) <
            (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2) ∧
        ((D.lostDegreeVertices (sourceSmallPrimes a x)
          (1 / Real.log (Real.log (x : ℝ)) ^ 3) b).card : ℝ) <
            (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2) := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_sourceSurvivorVertices_tail_le ha hc,
    eventually_source_badPrimeCount_tail_le hc he,
    eventually_actualSource_badPinnedVertexCount_tail_le ha hc he,
    eventually_source_lostDegreeCount_loglog_tail hc he,
    eventually_sourceSmallPrimes_le ha,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (4 : ℝ))] with
      x hsurv hprime hpin hlost hupper hL hl
  change 4 < Real.log (Real.log (x : ℝ)) at hl
  intro D
  let S := sourceSmallPrimes a x
  let L := Real.log (x : ℝ)
  let l := Real.log L
  let E : Fin 4 → ResidueAssignment S → Prop := fun i b =>
    if i = 0 then sourceSurvivorMean a c x / l ≤
        |((sourceSurvivorVertices a c x b).card : ℝ) - sourceSurvivorMean a c x|
    else if i = 1 then 4 * (x : ℝ) / L ^ 4 ≤ ((D.badTuplePrimes S b).card : ℝ)
    else if i = 2 then (x : ℝ) / (L * l ^ 2) ≤ ((D.badPinnedVertices S b).card : ℝ)
    else (x : ℝ) / (L * l ^ 2) ≤ ((D.lostDegreeVertices S (1 / l ^ 3) b).card : ℝ)
  have hLpos : 0 < L := by dsimp only [L]; linarith
  have hlpos : 0 < l := by dsimp only [l, L]; linarith
  have hlcube : l ≤ L ^ 3 := by
    have hlogle : l ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
    exact hlogle.trans (by simpa only [pow_one] using
      (pow_le_pow_right₀ hL (by norm_num : 1 ≤ 3)))
  have hprime' := hprime D S (sourceSmallPrimes_prime a x) (sourceSmallPrimes_rough a x) hupper
  have hlost' := hlost D S (sourceSmallPrimes_prime a x) (sourceSmallPrimes_rough a x) hupper
  have hpin' := hpin D
  have htail (i : Fin 4) :
      (∑ b : ResidueAssignment S, if E i b then residueAssignmentMass S b else 0) ≤ 1 / l := by
    fin_cases i
    · simpa [E] using hsurv
    · simpa [E] using hprime'.trans (one_div_le_one_div_of_le hlpos hlcube)
    · simpa [E] using hpin'
    · simpa [E] using hlost'
  have hbad : (∑ i : Fin 4, ∑ b : ResidueAssignment S,
      if E i b then residueAssignmentMass S b else 0) < 1 := by
    calc
      _ ≤ ∑ _i : Fin 4, (1 / l) := Finset.sum_le_sum fun i _hi => htail i
      _ = 4 / l := by simp; ring
      _ < 1 := (div_lt_one hlpos).mpr hl
  obtain ⟨b, hb⟩ := finite_exists_avoid_events (residueAssignmentMass S) E
    (residueAssignmentMass_nonneg S)
    (residueAssignmentMass_sum (fun p hp => (sourceSmallPrimes_prime a x p hp).pos)) hbad
  refine ⟨b, ?_, ?_, ?_, ?_⟩
  · simpa [E] using hb 0
  · simpa [E] using hb 1
  · simpa [E] using hb 2
  · simpa [E] using hb 3

end

end Erdos4b.FGKMT
