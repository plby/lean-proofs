/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ProfileWeightUpper

/-!
# Uniform upper bound for a constrained profile continuation

HLOZ Remark A.9 requires a bound uniform in the crossing count at the
separating annulus.  This file proves the discrete A.11/A.12 part of that
statement.  We fix an exact constrained prefix and sum the critical
negative-binomial transition weights of all admissible continuations.

The prefix is used only to determine the starting deviation.  Injectivity of
`profileSplit` removes the prefix multiplicity from the Gaussian partition
sum, giving a genuinely conditional tail estimate rather than the upper
bound for the full profile mass.
-/

open scoped BigOperators

namespace Erdos1165.ProfileConditionalTailUpper

open AppendixFirstMoment GaussianMultiBlockProfile ProfileA11Assembly
open ProfileListExponent ProfileWeightUpper

noncomputable section

/-- Exact transition mass of all constrained continuations of one fixed
profile prefix. -/
def constrainedProfileTailWeight
    (n start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ) : ℝ :=
  ∑ m ∈ (constrainedProfiles n delta).filter
      (fun m ↦ profilePrefix hstart hstartn m = pref),
    transitionSegmentProduct start (n - start) (profileAtScale m)

lemma constrainedProfileTailWeight_nonneg
    (n start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ) :
    0 ≤ constrainedProfileTailWeight n start hstart hstartn pref delta := by
  unfold constrainedProfileTailWeight
  exact Finset.sum_nonneg fun m _ ↦
    transitionSegmentProduct_nonneg start (n - start) (profileAtScale m)

lemma profileAtScale_profilePrefix_of_le
    {n start l : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (hlower : 2 ≤ l) (hupper : l ≤ start) (m : Profile n) :
    profileAtScale (profilePrefix hstart hstartn m) l =
      profileAtScale m l := by
  unfold profileAtScale
  rw [dif_pos ⟨hlower, hupper⟩,
    dif_pos ⟨hlower, hupper.trans hstartn⟩]
  rfl

/-- The exact Markov-product factorization of one full profile through one
fixed prefix. -/
theorem profileWeight_eq_prefix_mul_tail
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : Profile n) :
    profileWeight m =
      profileWeight (profilePrefix hstart hstartn m) *
        transitionSegmentProduct start (n - start) (profileAtScale m) := by
  rw [profileWeight_eq_transitionSegmentProduct (hstart.trans hstartn) m,
    profileWeight_eq_transitionSegmentProduct hstart]
  have hsteps : n - 2 = (start - 2) + (n - start) := by omega
  rw [hsteps, transitionSegmentProduct_append]
  rw [show 2 + (start - 2) = start by omega]
  congr 1
  rw [transitionSegmentProduct_eq_prod_Ico,
    transitionSegmentProduct_eq_prod_Ico]
  have htop : 2 + (start - 2) = start := by omega
  rw [htop]
  apply Finset.prod_congr rfl
  intro l hl
  have hl' := Finset.mem_Ico.mp hl
  rw [profileAtScale_profilePrefix_of_le hstart hstartn
      (by omega) hl'.2.le m,
    profileAtScale_profilePrefix_of_le hstart hstartn
      (by omega) hl'.2 m]

/-- Exact finite disintegration of the constrained full profile mass over
its one-copy exact prefixes.  Every continuation appears in exactly one
fiber of `profilePrefix`. -/
theorem constrainedProfileWeight_eq_sum_prefix_mul_tail
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (delta : ℝ) :
    constrainedProfileWeight n delta =
      ∑ pref ∈ constrainedProfiles start delta,
        profileWeight pref *
          constrainedProfileTailWeight n start hstart hstartn pref delta := by
  classical
  let F : Finset (Profile n) := constrainedProfiles n delta
  let P : Finset (Profile start) := constrainedProfiles start delta
  let e : Profile n → Profile start := profilePrefix hstart hstartn
  let tail : Profile n → ℝ := fun m ↦
    transitionSegmentProduct start (n - start) (profileAtScale m)
  have hmap : ∀ m ∈ F, e m ∈ P := by
    intro m hm
    exact profilePrefix_mem hstart hstartn hm
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun m ↦ profileWeight (e m) * tail m)
  unfold constrainedProfileWeight
  change (∑ m ∈ F, profileWeight m) = _
  calc
    (∑ m ∈ F, profileWeight m) =
        ∑ m ∈ F, profileWeight (e m) * tail m := by
      apply Finset.sum_congr rfl
      intro m hm
      exact profileWeight_eq_prefix_mul_tail hstart hstartn m
    _ = ∑ pref ∈ P, ∑ m ∈ F with e m = pref,
          profileWeight (e m) * tail m := hfiber.symm
    _ = ∑ pref ∈ P, profileWeight pref *
          constrainedProfileTailWeight n start hstart hstartn pref delta := by
      apply Finset.sum_congr rfl
      intro pref hpref
      unfold constrainedProfileTailWeight
      change (∑ m ∈ F with e m = pref,
          profileWeight (e m) * tail m) =
        profileWeight pref * ∑ m ∈ F with e m = pref, tail m
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]

private lemma fixedPrefix_future_injective
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) :
    Set.InjOn (profileFuture hstart hstartn)
      {m : Profile n | profilePrefix hstart hstartn m = pref} := by
  intro m hm q hq hfuture
  apply profileSplit_injective hstart hstartn
  apply Prod.ext
  · exact hm.trans hq.symm
  · exact hfuture

/-- With the prefix fixed, the Gaussian weight of all admissible future
tuples has no factor counting possible prefixes. -/
theorem sum_fixedPrefix_gaussianSegmentProduct_le
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ) :
    (∑ m ∈ (constrainedProfiles n delta).filter
          (fun m ↦ profilePrefix hstart hstartn m = pref),
        gaussianSegmentProduct start (n - start)
          (profileIntegerDeviation m)) ≤
      Real.exp (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
  let F : Finset (Profile n) :=
    (constrainedProfiles n delta).filter
      (fun m ↦ profilePrefix hstart hstartn m = pref)
  let Q : Finset (Fin (n - start) → ℕ) :=
    Fintype.piFinset (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  let e : Profile n → (Fin (n - start) → ℕ) :=
    profileFuture hstart hstartn
  let x : ℤ := profileIntegerDeviation pref start
  let w : (Fin (n - start) → ℕ) → ℝ :=
    gaussianFutureTupleWeight start x
  have he : Set.InjOn e F := by
    intro m hm q hq hmq
    apply fixedPrefix_future_injective hstart hstartn pref
    · exact (Finset.mem_filter.mp hm).2
    · exact (Finset.mem_filter.mp hq).2
    · exact hmq
  have himage : F.image e ⊆ Q := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨m, hm, rfl⟩ := hp
    have hmConstrained : m ∈ constrainedProfiles n delta :=
      (Finset.mem_filter.mp hm).1
    exact profileFuture_mem hstart hstartn hmConstrained
  have hw0 : ∀ p, 0 ≤ w p := fun p ↦
    gaussianFutureTupleWeight_nonneg start x p
  have hweight : ∀ m ∈ F,
      gaussianSegmentProduct start (n - start)
          (profileIntegerDeviation m) = w (e m) := by
    intro m hm
    have hprefix := (Finset.mem_filter.mp hm).2
    rw [gaussianSegmentProduct_eq_splitWeight hstart hstartn m]
    dsimp only [w, e, x]
    rw [hprefix]
  change (∑ m ∈ F,
      gaussianSegmentProduct start (n - start)
        (profileIntegerDeviation m)) ≤ _
  calc
    (∑ m ∈ F, gaussianSegmentProduct start (n - start)
        (profileIntegerDeviation m)) = ∑ m ∈ F, w (e m) := by
      apply Finset.sum_congr rfl
      exact hweight
    _ = ∑ p ∈ F.image e, w p := by
      symm
      exact Finset.sum_image he
    _ ≤ ∑ p ∈ Q, w p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p _hp _hnot ↦ hw0 p)
    _ ≤ Real.exp (∑ j ∈ Finset.Ico start
        (start + (n - start)), 1 / (j : ℝ)) := by
      exact sum_gaussianFutureTupleWeight_le (n - start) start
        (by omega) x (allowedValues delta)
    _ = Real.exp (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
      rw [Nat.add_sub_of_le hstartn]

/-- Uniform A.11/A.12 upper bound for every exact admissible prefix at or
beyond the checked Taylor cutoff. -/
theorem constrainedProfileTailWeight_le_exp
    {n start : ℕ}
    (htail : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (pref : Profile start) :
    constrainedProfileTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htail)
        hstartn pref
        profileUpperDelta ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
        ∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
  let hstart : 2 ≤ start :=
    (show 2 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans htail
  let F : Finset (Profile n) :=
    (constrainedProfiles n profileUpperDelta).filter
      (fun m ↦ profilePrefix hstart hstartn m = pref)
  let A : ℝ := Real.exp (-(2 * (n - start : ℕ) : ℝ) +
    a11ErrorCoefficient profileUpperDelta 2 1 11 *
      (n : ℝ) ^ (3 * profileUpperDelta) + 4)
  have hpoint : ∀ m ∈ F,
      transitionSegmentProduct start (n - start) (profileAtScale m) ≤
        A * gaussianSegmentProduct start (n - start)
          (profileIntegerDeviation m) := by
    intro m hm
    have hmConstrained : IsConstrainedProfile profileUpperDelta m :=
      mem_constrainedProfiles.mp (Finset.mem_filter.mp hm).1
    have cert := constrainedProfileUpperCertificate
      (htail.trans hstartn) hmConstrained
    have hsubsetIco : Finset.Ico start n ⊆
        Finset.Ico profileUpperTailStart n := by
      intro l hl
      rw [Finset.mem_Ico] at hl ⊢
      exact ⟨htail.trans hl.1, hl.2⟩
    have hsubsetIcc : Finset.Icc start n ⊆
        Finset.Icc profileUpperTailStart n := by
      intro l hl
      rw [Finset.mem_Icc] at hl ⊢
      exact ⟨htail.trans hl.1, hl.2⟩
    exact transitionSegmentProduct_le_a11_gaussian_from
      start n hstart hstartn (profileAtScale m)
      (profileIntegerDeviation m)
      (delta := profileUpperDelta) (A := 2) (B := 1) (C := 11)
      (by norm_num [profileUpperDelta])
      (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num)
      (by norm_num)
      (fun l hl ↦ cert.entry_two_le l (hsubsetIco hl))
      (fun l hl ↦ cert.taylorWindow l (hsubsetIco hl))
      (fun l hl ↦ cert.base l (hsubsetIco hl))
      (fun l hl ↦ cert.close l (hsubsetIco hl))
      (fun l hl ↦ cert.moderate l (hsubsetIco hl))
      (fun l hl ↦ cert.increment l (hsubsetIco hl))
      (profileAtScale_real_eq_center_add_deviation m)
      (fun l hl ↦ by
        simpa only [one_mul] using cert.deviation l (hsubsetIcc hl))
      (fun l hl ↦ cert.deviationIncrement l (hsubsetIco hl))
  have hA0 : 0 ≤ A := Real.exp_pos _ |>.le
  have hgauss := sum_fixedPrefix_gaussianSegmentProduct_le
    hstart hstartn pref profileUpperDelta
  unfold constrainedProfileTailWeight
  change (∑ m ∈ F,
      transitionSegmentProduct start (n - start) (profileAtScale m)) ≤ _
  calc
    (∑ m ∈ F,
        transitionSegmentProduct start (n - start) (profileAtScale m)) ≤
        ∑ m ∈ F,
          A * gaussianSegmentProduct start (n - start)
            (profileIntegerDeviation m) :=
      Finset.sum_le_sum hpoint
    _ = A * (∑ m ∈ F,
          gaussianSegmentProduct start (n - start)
            (profileIntegerDeviation m)) := by
      rw [Finset.mul_sum]
    _ ≤ A * Real.exp
          (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) :=
      mul_le_mul_of_nonneg_left hgauss hA0
    _ = Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
        ∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
      rw [Real.exp_add]

/-- Exact Markov disintegration of one constrained continuation through an
intermediate retained prefix.  The initial transition mass is kept with the
intermediate prefix, so summing padded suffix rows introduces no prefix
multiplicity. -/
theorem constrainedProfileTailWeight_eq_sum_intermediatePrefix
    {n start mid : ℕ}
    (hstart : 2 ≤ start) (hstartmid : start ≤ mid) (hmidn : mid ≤ n)
    (pref : Profile start) (delta : ℝ) :
    constrainedProfileTailWeight n start hstart (hstartmid.trans hmidn)
        pref delta =
      ∑ midPref ∈ (constrainedProfiles mid delta).filter
          (fun q ↦ profilePrefix hstart hstartmid q = pref),
        transitionSegmentProduct start (mid - start)
            (profileAtScale midPref) *
          constrainedProfileTailWeight n mid (hstart.trans hstartmid) hmidn
            midPref delta := by
  classical
  let hmid : 2 ≤ mid := hstart.trans hstartmid
  let hstartn : start ≤ n := hstartmid.trans hmidn
  let F : Finset (Profile n) :=
    (constrainedProfiles n delta).filter
      (fun m ↦ profilePrefix hstart hstartn m = pref)
  let P : Finset (Profile mid) :=
    (constrainedProfiles mid delta).filter
      (fun q ↦ profilePrefix hstart hstartmid q = pref)
  let e : Profile n → Profile mid := profilePrefix hmid hmidn
  let initial : Profile n → ℝ := fun m ↦
    transitionSegmentProduct start (mid - start) (profileAtScale m)
  let future : Profile n → ℝ := fun m ↦
    transitionSegmentProduct mid (n - mid) (profileAtScale m)
  have hprefix_comp (m : Profile n) :
      profilePrefix hstart hstartmid (e m) =
        profilePrefix hstart hstartn m := by
    funext i
    rfl
  have hmap : ∀ m ∈ F, e m ∈ P := by
    intro m hm
    rw [Finset.mem_filter]
    constructor
    · exact profilePrefix_mem hmid hmidn (Finset.mem_filter.mp hm).1
    · rw [hprefix_comp]
      exact (Finset.mem_filter.mp hm).2
  have hinitial (m : Profile n) :
      initial m =
        transitionSegmentProduct start (mid - start)
          (profileAtScale (e m)) := by
    unfold initial e
    rw [transitionSegmentProduct_eq_prod_Ico,
      transitionSegmentProduct_eq_prod_Ico]
    apply Finset.prod_congr rfl
    intro l hl
    have hlIco := Finset.mem_Ico.mp hl
    have hltmid : l < mid := by omega
    rw [profileAtScale_profilePrefix_of_le hmid hmidn
        (hstart.trans hlIco.1) hltmid.le,
      profileAtScale_profilePrefix_of_le hmid hmidn
        (by omega) (by omega)]
  have hfactor (m : Profile n) :
      transitionSegmentProduct start (n - start) (profileAtScale m) =
        initial m * future m := by
    have hsteps : n - start = (mid - start) + (n - mid) := by omega
    rw [hsteps, transitionSegmentProduct_append]
    rw [show start + (mid - start) = mid by omega]
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap
    (fun m ↦ initial m * future m)
  unfold constrainedProfileTailWeight
  change (∑ m ∈ F,
      transitionSegmentProduct start (n - start) (profileAtScale m)) = _
  calc
    (∑ m ∈ F,
        transitionSegmentProduct start (n - start) (profileAtScale m)) =
        ∑ m ∈ F, initial m * future m := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact hfactor m
    _ = ∑ midPref ∈ P, ∑ m ∈ F with e m = midPref,
          initial m * future m := hfiber.symm
    _ = ∑ midPref ∈ P,
          transitionSegmentProduct start (mid - start)
              (profileAtScale midPref) *
            ∑ m ∈ F with e m = midPref, future m := by
      apply Finset.sum_congr rfl
      intro midPref _hmidPref
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hem : e m = midPref := (Finset.mem_filter.mp hm).2
      rw [← hem, ← hinitial]
    _ = ∑ midPref ∈ P,
          transitionSegmentProduct start (mid - start)
              (profileAtScale midPref) *
            constrainedProfileTailWeight n mid hmid hmidn midPref delta := by
      apply Finset.sum_congr rfl
      intro midPref hmidPref
      congr 1
      unfold constrainedProfileTailWeight
      apply Finset.sum_congr
      · ext m
        simp only [F, e, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hm, _hstartPref⟩, hmidPrefEq⟩
          exact ⟨hm, hmidPrefEq⟩
        · rintro ⟨hm, hmidPrefEq⟩
          refine ⟨⟨hm, ?_⟩, hmidPrefEq⟩
          rw [← (Finset.mem_filter.mp hmidPref).2]
          rw [← hmidPrefEq, hprefix_comp]
      · intro m _hm
        rfl
    _ = _ := by rfl

/-- A uniform bound on every continuation beyond an intermediate scale keeps
the exact transition mass up to that scale.  This is the weighted form of
Markov disintegration needed when a padded stopped-word row supplies the
intermediate prefix distribution. -/
theorem coefficient_mul_constrainedProfileTailWeight_le_intermediate
    {n start mid : ℕ}
    (hstart : 2 ≤ start) (hstartmid : start ≤ mid) (hmidn : mid ≤ n)
    (pref : Profile start) (delta coefficient bound : ℝ)
    (hfuture : ∀ midPref ∈ (constrainedProfiles mid delta).filter
        (fun q ↦ profilePrefix hstart hstartmid q = pref),
      coefficient * constrainedProfileTailWeight n mid
        (hstart.trans hstartmid) hmidn midPref delta ≤ bound) :
    coefficient * constrainedProfileTailWeight n start hstart
        (hstartmid.trans hmidn) pref delta ≤
      bound * constrainedProfileTailWeight mid start hstart hstartmid
        pref delta := by
  rw [constrainedProfileTailWeight_eq_sum_intermediatePrefix
    hstart hstartmid hmidn pref delta]
  rw [Finset.mul_sum]
  calc
    ∑ midPref ∈ (constrainedProfiles mid delta).filter
          (fun q ↦ profilePrefix hstart hstartmid q = pref),
        coefficient *
          (transitionSegmentProduct start (mid - start)
              (profileAtScale midPref) *
            constrainedProfileTailWeight n mid
              (hstart.trans hstartmid) hmidn midPref delta) ≤
        ∑ midPref ∈ (constrainedProfiles mid delta).filter
          (fun q ↦ profilePrefix hstart hstartmid q = pref),
        transitionSegmentProduct start (mid - start)
            (profileAtScale midPref) * bound := by
      apply Finset.sum_le_sum
      intro midPref hmidPref
      calc
        coefficient *
            (transitionSegmentProduct start (mid - start)
                (profileAtScale midPref) *
              constrainedProfileTailWeight n mid
                (hstart.trans hstartmid) hmidn midPref delta) =
            transitionSegmentProduct start (mid - start)
                (profileAtScale midPref) *
              (coefficient * constrainedProfileTailWeight n mid
                (hstart.trans hstartmid) hmidn midPref delta) := by ring
        _ ≤ transitionSegmentProduct start (mid - start)
              (profileAtScale midPref) * bound :=
          mul_le_mul_of_nonneg_left (hfuture midPref hmidPref)
            (transitionSegmentProduct_nonneg start (mid - start)
              (profileAtScale midPref))
    _ = bound * constrainedProfileTailWeight mid start hstart
          hstartmid pref delta := by
      rw [mul_comm bound]
      rw [← Finset.sum_mul]
      rfl

end

end Erdos1165.ProfileConditionalTailUpper
