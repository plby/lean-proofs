/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos1165.BufferedProfileCostUpper
import ErdosProblems.Erdos1165.ProfilePrefixFutureEquiv

/-!
# Markov decomposition of a buffered profile

This module isolates the finite-coordinate reindexing used to sum the
three erased separation coordinates.  The local transition product is the
literal tilted critical branching-chain weight, while the coordinates on
the two sides remain ordinary constrained profile pieces.
-/

open scoped BigOperators ENNReal

namespace Erdos1165.BufferedProfileMarkovUpper

open AppendixFirstMoment AnnularRadialProfileWords
open BufferedProfileCostUpper BufferedStoppedSuccessfulPointEvent
open BufferedSuccessfulProfile ProfileListExponent ProfileWeightUpper
open ProfilePrefixFutureEquiv TiltedProfileTransitionBridge

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Split a tuple of length `a+b` into its first `a` and last `b`
coordinates. -/
def tupleSplitEquiv (a b : ℕ) :
    (Fin (a + b) → ℕ) ≃ (Fin a → ℕ) × (Fin b → ℕ) :=
  (Equiv.piCongrLeft (fun _ : Fin (a + b) ↦ ℕ)
    (finSumFinEquiv (m := a) (n := b))).symm.trans
      (Equiv.sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b ↦ ℕ))

/-- The same tuple split when the source length is propositionally equal
to `a+b`. -/
def tupleSplitEquivOfEq {c : ℕ} (a b : ℕ) (h : c = a + b) :
    (Fin c → ℕ) ≃ (Fin a → ℕ) × (Fin b → ℕ) :=
  (Equiv.piCongrLeft (fun _ : Fin (a + b) ↦ ℕ) (finCongr h)).trans
    (tupleSplitEquiv a b)

/-- A profile as a prefix, a finite bridge, and the remaining future. -/
def profileThreeSplitEquiv {n start steps : ℕ}
    (hstart : 2 ≤ start) (hstop : start + steps ≤ n) :
    Profile n ≃ Profile start ×
      ((Fin steps → ℕ) × (Fin (n - (start + steps)) → ℕ)) := by
  have hstartn : start ≤ n := by omega
  have hlen : n - start = steps + (n - (start + steps)) := by omega
  exact (profileSplitEquiv hstart hstartn).trans
    (Equiv.prodCongr (Equiv.refl _)
      (tupleSplitEquivOfEq steps (n - (start + steps)) hlen))

@[simp] theorem profileThreeSplitEquiv_fst
    {n start steps : ℕ} (hstart : 2 ≤ start)
    (hstop : start + steps ≤ n) (m : Profile n) :
    (profileThreeSplitEquiv hstart hstop m).1 =
      profilePrefix hstart (by omega) m := by
  rfl

@[simp] theorem profileThreeSplitEquiv_bridge_apply
    {n start steps : ℕ} (hstart : 2 ≤ start)
    (hstop : start + steps ≤ n) (m : Profile n) (i : Fin steps) :
    (profileThreeSplitEquiv hstart hstop m).2.1 i =
      profileFuture hstart (by omega) m
        ⟨i.1, by have := i.2; omega⟩ := by
  simp [profileThreeSplitEquiv, tupleSplitEquivOfEq, tupleSplitEquiv,
    Equiv.piCongrLeft, finSumFinEquiv]
  change m _ = m _
  congr 1

@[simp] theorem profileThreeSplitEquiv_tail_apply
    {n start steps : ℕ} (hstart : 2 ≤ start)
    (hstop : start + steps ≤ n) (m : Profile n)
    (i : Fin (n - (start + steps))) :
    (profileThreeSplitEquiv hstart hstop m).2.2 i =
      profileFuture hstart (by omega) m
        ⟨steps + i.1, by have := i.2; omega⟩ := by
  simp [profileThreeSplitEquiv, tupleSplitEquivOfEq, tupleSplitEquiv,
    Equiv.piCongrLeft, finSumFinEquiv]
  change m _ = m _
  congr 1

/-- Product of the transition kernels along one literal finite path. -/
def pathTransitionProduct : (steps : ℕ) → ℕ →
    (Fin steps → ℕ) → ℝ
  | 0, _a, _path => 1
  | steps + 1, a, path =>
      transitionMass a (path 0) *
        pathTransitionProduct steps (path 0) (Fin.tail path)

/-- The recursive path product is the ordinary transition product after
prepending its initial state. -/
theorem pathTransitionProduct_eq_transitionProduct_cons :
    ∀ (steps a : ℕ) (path : Fin steps → ℕ),
      pathTransitionProduct steps a path =
        transitionProduct (a :: List.ofFn path) := by
  intro steps
  induction steps with
  | zero =>
      intro a path
      simp [pathTransitionProduct, transitionProduct]
  | succ steps ih =>
      intro a path
      rw [pathTransitionProduct, List.ofFn_succ,
        transitionProduct_cons_cons, ih]
      have htail : Fin.tail path = fun i => path i.succ := by
        funext i
        rfl
      rw [htail]

theorem transitionMass_mul_transitionProduct_ofFn_eq_path
    {steps a : ℕ} (hsteps : 0 < steps) (path : Fin steps → ℕ) :
    transitionMass a (path ⟨0, hsteps⟩) *
        transitionProduct (List.ofFn path) =
      pathTransitionProduct steps a path := by
  cases steps with
  | zero => simp at hsteps
  | succ steps =>
      rw [pathTransitionProduct, List.ofFn_succ]
      have hzero : (⟨0, Nat.zero_lt_succ steps⟩ : Fin (steps + 1)) = 0 := rfl
      rw [hzero]
      congr 1
      rw [pathTransitionProduct_eq_transitionProduct_cons]
      congr 1

lemma pathTransitionProduct_nonneg (steps a : ℕ)
    (path : Fin steps → ℕ) :
    0 ≤ pathTransitionProduct steps a path := by
  induction steps generalizing a with
  | zero => simp [pathTransitionProduct]
  | succ steps ih =>
      rw [pathTransitionProduct]
      exact mul_nonneg (transitionMass_nonneg _ _) (ih _ _)

/-- The recursive tilted path weight is exactly the transition product
times the exponential tilt of all visited coordinates. -/
theorem tiltedPathWeightENNReal_eq_ofReal : ∀ steps (r : ℝ),
    0 ≤ r → ∀ (a : ℕ) (path : Fin steps → ℕ),
      tiltedPathWeightENNReal steps r a path =
        ENNReal.ofReal
          (r ^ (∑ i, path i) * pathTransitionProduct steps a path) := by
  intro steps
  induction steps with
  | zero =>
      intro r _hr a path
      simp [tiltedPathWeightENNReal, pathTransitionProduct]
  | succ steps ih =>
      intro r hr a path
      rw [tiltedPathWeightENNReal, pathTransitionProduct,
        ih r hr (path 0) (Fin.tail path)]
      rw [Fin.sum_univ_succ]
      rw [pow_add]
      rw [← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hr (path 0))
        (transitionMass_nonneg a (path 0)))]
      have hsumtail :
          (∑ i : Fin steps, Fin.tail path i) =
            ∑ i : Fin steps, path i.succ := by rfl
      rw [hsumtail]
      congr 1
      ring

@[simp] lemma tiltParameter_one : ∀ steps : ℕ,
    tiltParameter steps 1 = 1 := by
  intro steps
  induction steps with
  | zero => simp [tiltParameter]
  | succ steps ih => norm_num [tiltParameter, ih]

/-- With no exponential tilt, all finite paths of the critical branching
chain have total mass one. -/
theorem tsum_pathTransitionProduct_eq_one (steps a : ℕ) :
    (∑' path : Fin steps → ℕ,
      ENNReal.ofReal (pathTransitionProduct steps a path)) = 1 := by
  have hconv : ∀ j < steps, (1 : ℝ) * tiltParameter j 1 < 2 := by
    intro j _hj
    simp
  have hsum := tsum_tiltedPathWeightENNReal_eq steps (1 : ℝ)
    (by norm_num) hconv a
  have hmass := tiltedPathMass_eq steps (1 : ℝ)
    (by norm_num) hconv a
  calc
    (∑' path : Fin steps → ℕ,
        ENNReal.ofReal (pathTransitionProduct steps a path)) =
        ∑' path : Fin steps → ℕ,
          tiltedPathWeightENNReal steps 1 a path := by
      apply tsum_congr
      intro path
      simpa using
        (tiltedPathWeightENNReal_eq_ofReal steps (1 : ℝ)
          (by norm_num) a path).symm
    _ = ENNReal.ofReal (tiltedPathMass steps 1 a) := hsum
    _ = 1 := by rw [hmass]; simp

/-- Reading consecutive entries of a profile gives the same literal path
product as `transitionSegmentProduct`. -/
theorem pathTransitionProduct_profile : ∀ steps {n start : ℕ}
    (m : Profile n),
    pathTransitionProduct steps (profileAtScale m start)
        (fun i ↦ profileAtScale m (start + 1 + i.1)) =
      transitionSegmentProduct start steps (profileAtScale m) := by
  intro steps
  induction steps with
  | zero =>
      intro n start m
      simp [pathTransitionProduct, transitionSegmentProduct]
  | succ steps ih =>
      intro n start m
      rw [pathTransitionProduct, transitionSegmentProduct]
      congr 1
      have htail :
          Fin.tail
              (fun i : Fin (steps + 1) ↦
                profileAtScale m (start + 1 + i.1)) =
            fun i : Fin steps ↦
              profileAtScale m ((start + 1) + 1 + i.1) := by
        funext i
        change profileAtScale m (start + 1 + (i.1 + 1)) = _
        congr 1
        omega
      rw [htail]
      exact ih (start := start + 1) m

/-- Coordinates erased between `low` and `high` are exactly the natural
scale interval `Ioo low high`. -/
theorem erasedProfileSum_eq_sum_Ioo
    {n low high : ℕ} (hlow : 2 ≤ low) (hhigh : high ≤ n + 1)
    (m : Profile n) :
    erasedProfileSum low high m =
      ∑ k ∈ Finset.Ioo low high, profileAtScale m k := by
  unfold erasedProfileSum
  let S := Finset.univ.filter
    (fun i : Fin (n - 1) ↦ ¬ RetainedCoordinate low high (scaleIndex i))
  change (∑ i ∈ S, m i) = _
  apply Finset.sum_bij (fun i _hi ↦ scaleIndex i)
  · intro i hi
    rw [Finset.mem_Ioo]
    have herased := (Finset.mem_filter.mp hi).2
    unfold RetainedCoordinate at herased
    omega
  · intro i hi j hj hij
    apply Fin.ext
    unfold scaleIndex at hij
    omega
  · intro k hk
    rw [Finset.mem_Ioo] at hk
    let i : Fin (n - 1) := ⟨k - 2, by omega⟩
    refine ⟨i, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold RetainedCoordinate scaleIndex
      dsimp only [i]
      omega
    · unfold scaleIndex
      dsimp only [i]
      omega
  · intro i hi
    rw [profileAtScale_scaleIndex]

/-- For the actual three-coordinate buffer, its erased sum is bounded by
the sum of the four bridge coordinates (the last one is the retained right
endpoint). -/
theorem erasedProfileSum_le_four_bridge_sum
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (m : Profile n) :
    erasedProfileSum low (low + 4) m ≤
      ∑ i : Fin 4, profileAtScale m (low + 1 + i.1) := by
  rw [erasedProfileSum_eq_sum_Ioo hlow (by omega) m]
  let S := Finset.univ.filter (fun i : Fin 4 ↦ i.1 < 3)
  have heq :
      (∑ k ∈ Finset.Ioo low (low + 4), profileAtScale m k) =
        ∑ i ∈ S, profileAtScale m (low + 1 + i.1) := by
    apply Finset.sum_bij (fun k hk ↦
      (⟨k - (low + 1), by
        have := (Finset.mem_Ioo.mp hk).2
        omega⟩ : Fin 4))
    · intro k hk
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have := Finset.mem_Ioo.mp hk
      dsimp
      omega
    · intro a ha b hb hab
      have ha' := Finset.mem_Ioo.mp ha
      have hb' := Finset.mem_Ioo.mp hb
      have hsub := congrArg Fin.val hab
      change a - (low + 1) = b - (low + 1) at hsub
      omega
    · intro i hi
      rw [Finset.mem_filter] at hi
      let k := low + 1 + i.1
      refine ⟨k, ?_, ?_⟩
      · rw [Finset.mem_Ioo]
        dsimp only [k]
        omega
      · apply Fin.ext
        dsimp only [k]
        omega
    · intro k hk
      apply congrArg (profileAtScale m)
      have := (Finset.mem_Ioo.mp hk).1
      change k = low + 1 + (k - (low + 1))
      omega
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ ↦ Nat.zero_le _)

/-- The low side of a buffered profile is an ordinary constrained prefix. -/
theorem buffered_profilePrefix_mem
    {n low high : ℕ} (hlow : 2 ≤ low) (hlown : low ≤ n)
    {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    profilePrefix hlow hlown m ∈ constrainedProfiles low delta := by
  rw [mem_constrainedProfiles]
  intro i
  let j : Fin (n - 1) := ⟨i.1, by have := i.2; omega⟩
  have hretained : RetainedCoordinate low high (scaleIndex j) := Or.inl (by
    unfold scaleIndex
    dsimp only [j]
    have hi := i.2
    omega)
  have hj := hm j hretained
  unfold InProfileWindow profileCenter
  simpa [profilePrefix, scaleIndex, j] using hj

/-- Every coordinate strictly after the high endpoint lies in its usual
constrained window. -/
theorem buffered_profileFuture_mem
    {n low high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    profileFuture hhigh hhighn m ∈
      Fintype.piFinset (fun i : Fin (n - high) ↦
        allowedValues delta (high + 1 + i.1)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_allowedValues]
  let j : Fin (n - 1) :=
    ⟨high - 1 + i.1, by have := i.2; omega⟩
  have hj := hm j (Or.inr (by
    unfold scaleIndex
    dsimp only [j]
    omega))
  have hscale : scaleIndex j = high + 1 + i.1 := by
    unfold scaleIndex
    dsimp only [j]
    omega
  change InProfileWindow delta (high + 1 + i.1)
    (profileFuture hhigh hhighn m i)
  unfold InProfileWindow profileCenter profileFuture
  change |(m j : ℝ) - ((2 * (high + 1 + i.1) ^ 2 : ℕ) : ℝ)| ≤ _
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [hscale] using hj

/-- The retained high endpoint itself is constrained. -/
theorem buffered_high_mem_allowedValues
    {n low high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    profileAtScale m high ∈ allowedValues delta high := by
  rw [mem_allowedValues]
  let j : Fin (n - 1) := ⟨high - 2, by omega⟩
  have hscale : scaleIndex j = high := by
    unfold scaleIndex
    dsimp only [j]
    omega
  have hj := hm j (Or.inr hscale.symm.le)
  unfold InProfileWindow profileCenter
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [← hscale, profileAtScale_scaleIndex] using hj

@[simp] theorem profileThreeSplitEquiv_bridge_eq_profileAtScale
    {n start steps : ℕ} (hstart : 2 ≤ start)
    (hstop : start + steps ≤ n) (m : Profile n) (i : Fin steps) :
    (profileThreeSplitEquiv hstart hstop m).2.1 i =
      profileAtScale m (start + 1 + i.1) := by
  rw [profileThreeSplitEquiv_bridge_apply]
  rw [profileAtScale, dif_pos (by constructor <;> omega)]
  unfold profileFuture
  congr 1
  apply Fin.ext
  change start - 1 + i.1 = (start + 1 + i.1) - 2
  omega

@[simp] theorem profileThreeSplitEquiv_tail_eq_profileAtScale
    {n start steps : ℕ} (hstart : 2 ≤ start)
    (hstop : start + steps ≤ n) (m : Profile n)
    (i : Fin (n - (start + steps))) :
    (profileThreeSplitEquiv hstart hstop m).2.2 i =
      profileAtScale m (start + steps + 1 + i.1) := by
  rw [profileThreeSplitEquiv_tail_apply]
  rw [profileAtScale, dif_pos (by constructor <;> omega)]
  unfold profileFuture
  congr 1
  apply Fin.ext
  change start - 1 + (steps + i.1) =
    (start + steps + 1 + i.1) - 2
  omega

/-- A constrained canonical prefix with a prescribed retained endpoint. -/
def endpointCenterProfile (start a : ℕ) : Profile start :=
  fun i ↦ if scaleIndex i = start then a else profileCenter (scaleIndex i)

@[simp] theorem endpointCenterProfile_at_end
    {start a : ℕ} (hstart : 2 ≤ start) :
    profileAtScale (endpointCenterProfile start a) start = a := by
  rw [profileAtScale, dif_pos ⟨hstart, le_rfl⟩]
  simp [endpointCenterProfile, scaleIndex, show start - 2 + 2 = start by omega]

theorem endpointCenterProfile_mem
    {start a : ℕ} (hstart : 2 ≤ start) {delta : ℝ}
    (ha : a ∈ allowedValues delta start) :
    endpointCenterProfile start a ∈ constrainedProfiles start delta := by
  rw [mem_constrainedProfiles]
  intro i
  unfold endpointCenterProfile
  split_ifs with hi
  · rw [hi]
    exact mem_allowedValues.mp ha
  · unfold InProfileWindow
    simp only [sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) _

/-- Tail mass depending only on the crossing count at `start`. -/
def endpointTailWeight
    (n start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (a : ℕ) (delta : ℝ) : ℝ :=
  ∑ future ∈ Fintype.piFinset
      (fun i : Fin (n - start) ↦
        allowedValues delta (start + 1 + i.1)),
    transitionSegmentProduct start (n - start)
      (profileAtScale
        (extendProfile hstart hstartn
          (endpointCenterProfile start a) future))

/-- One literal future summand in `endpointTailWeight`. -/
def endpointTailTerm
    (n start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (a : ℕ) (future : Fin (n - start) → ℕ) : ℝ :=
  transitionSegmentProduct start (n - start)
    (profileAtScale
      (extendProfile hstart hstartn
        (endpointCenterProfile start a) future))

/-- A fixed-endpoint continuation is the literal Markov path product
started from that endpoint. -/
theorem endpointTailTerm_eq_pathTransitionProduct
    {n start a : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (future : Fin (n - start) → ℕ) :
    endpointTailTerm n start hstart hstartn a future =
      pathTransitionProduct (n - start) a future := by
  let m := extendProfile hstart hstartn
    (endpointCenterProfile start a) future
  have hbase : profileAtScale m start = a := by
    have h := profileAtScale_profilePrefix hstart hstartn m
    rw [profilePrefix_extendProfile] at h
    exact h.symm.trans (endpointCenterProfile_at_end hstart)
  have hfuture : ∀ i : Fin (n - start),
      profileAtScale m (start + 1 + i.1) = future i := by
    intro i
    have h := profileFuture_eq_profileAtScale hstart hstartn m i
    rw [profileFuture_extendProfile] at h
    exact h.symm
  unfold endpointTailTerm
  change transitionSegmentProduct start (n - start) (profileAtScale m) = _
  rw [← pathTransitionProduct_profile (steps := n - start)
    (start := start) m]
  rw [hbase]
  congr 1
  funext i
  exact hfuture i

/-- Restricting a Markov continuation to the profile window can only lose
mass. -/
theorem endpointTailWeight_le_one
    {n start a : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (delta : ℝ) :
    endpointTailWeight n start hstart hstartn a delta ≤ 1 := by
  let F := Fintype.piFinset
    (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  rw [← ENNReal.ofReal_le_one]
  unfold endpointTailWeight
  change ENNReal.ofReal
      (∑ future ∈ F,
        transitionSegmentProduct start (n - start)
          (profileAtScale
            (extendProfile hstart hstartn
              (endpointCenterProfile start a) future))) ≤ 1
  rw [ENNReal.ofReal_sum_of_nonneg]
  · calc
      (∑ future ∈ F,
          ENNReal.ofReal
            (transitionSegmentProduct start (n - start)
              (profileAtScale
                (extendProfile hstart hstartn
                  (endpointCenterProfile start a) future)))) =
          ∑ future ∈ F,
            ENNReal.ofReal
              (pathTransitionProduct (n - start) a future) := by
        apply Finset.sum_congr rfl
        intro future _hfuture
        rw [← endpointTailTerm_eq_pathTransitionProduct hstart hstartn future]
        rfl
      _ ≤ ∑' future : Fin (n - start) → ℕ,
          ENNReal.ofReal
            (pathTransitionProduct (n - start) a future) :=
        ENNReal.summable.sum_le_tsum F (fun _ _ ↦ bot_le)
      _ = 1 := tsum_pathTransitionProduct_eq_one (n - start) a
  · intro future _hfuture
    exact transitionSegmentProduct_nonneg start (n - start) _

/-- Any constrained continuation from a fixed admissible prefix has total
Markov mass at most one. -/
theorem constrainedProfileTailWeight_le_one
    {n start : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (pref : Profile start) (delta : ℝ)
    (hpref : pref ∈ constrainedProfiles start delta) :
    ProfileConditionalTailUpper.constrainedProfileTailWeight
        n start hstart hstartn pref delta ≤ 1 := by
  rw [ProfilePrefixFutureEquiv.constrainedProfileTailWeight_eq_sum_future
    hstart hstartn pref delta hpref]
  rw [← ENNReal.ofReal_le_one]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · calc
      (∑ future ∈ Fintype.piFinset
            (fun i : Fin (n - start) ↦
              allowedValues delta (start + 1 + i.1)),
          ENNReal.ofReal
            (transitionSegmentProduct start (n - start)
              (profileAtScale
                (extendProfile hstart hstartn pref future)))) =
          ∑ future ∈ Fintype.piFinset
              (fun i : Fin (n - start) ↦
                allowedValues delta (start + 1 + i.1)),
            ENNReal.ofReal
              (pathTransitionProduct (n - start)
                (profileAtScale pref start) future) := by
        apply Finset.sum_congr rfl
        intro future _hfuture
        congr 1
        let m := extendProfile hstart hstartn pref future
        have hbase : profileAtScale m start = profileAtScale pref start := by
          have h := profileAtScale_profilePrefix hstart hstartn m
          rw [profilePrefix_extendProfile] at h
          exact h.symm
        have hfuture : ∀ i : Fin (n - start),
            profileAtScale m (start + 1 + i.1) = future i := by
          intro i
          have h := profileFuture_eq_profileAtScale hstart hstartn m i
          rw [profileFuture_extendProfile] at h
          exact h.symm
        change transitionSegmentProduct start (n - start)
            (profileAtScale m) = _
        rw [← pathTransitionProduct_profile (steps := n - start)
          (start := start) m]
        rw [hbase]
        congr 1
        funext i
        exact hfuture i
      _ ≤ ∑' future : Fin (n - start) → ℕ,
          ENNReal.ofReal
            (pathTransitionProduct (n - start)
              (profileAtScale pref start) future) :=
        ENNReal.summable.sum_le_tsum _ (fun _ _ ↦ bot_le)
      _ = 1 := tsum_pathTransitionProduct_eq_one (n - start)
        (profileAtScale pref start)
  · intro future _hfuture
    exact transitionSegmentProduct_nonneg start (n - start) _

/-- Explicit uniform envelope for a constrained continuation beginning at
`start`. -/
def conditionalTailEnvelope (n start : ℕ) : ℝ :=
  Real.exp (-(2 * (n - start : ℕ) : ℝ) +
    ProfileA11Assembly.a11ErrorCoefficient profileUpperDelta 2 1 11 *
      (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
    ∑ j ∈ Finset.Ico start n, 1 / (j : ℝ))

lemma conditionalTailEnvelope_nonneg (n start : ℕ) :
    0 ≤ conditionalTailEnvelope n start :=
  Real.exp_nonneg _

theorem endpointTailWeight_eq_constrainedProfileTailWeight
    {n start a : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    {delta : ℝ} (ha : a ∈ allowedValues delta start) :
    endpointTailWeight n start hstart hstartn a delta =
      ProfileConditionalTailUpper.constrainedProfileTailWeight
        n start hstart hstartn (endpointCenterProfile start a) delta := by
  rw [ProfilePrefixFutureEquiv.constrainedProfileTailWeight_eq_sum_future
    hstart hstartn (endpointCenterProfile start a) delta
    (endpointCenterProfile_mem hstart ha)]
  rfl

set_option linter.constructorNameAsVariable false in
/-- Before the Taylor cutoff, disintegrate through the cutoff and use only
the Markov subprobability bound on the initial constrained segment. -/
theorem endpointTailWeight_le_envelope_from_cutoff
    {n start a : ℕ} (hstart : 2 ≤ start)
    (hstartCutoff : start ≤ profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n)
    (ha : a ∈ allowedValues profileUpperDelta start) :
    endpointTailWeight n start hstart
        (hstartCutoff.trans hcutoffn) a profileUpperDelta ≤
      conditionalTailEnvelope n profileUpperTailStart := by
  let pref := endpointCenterProfile start a
  have hpref : pref ∈ constrainedProfiles start profileUpperDelta :=
    endpointCenterProfile_mem hstart ha
  rw [endpointTailWeight_eq_constrainedProfileTailWeight
    hstart (hstartCutoff.trans hcutoffn) ha]
  have hdis :=
    ProfileConditionalTailUpper.coefficient_mul_constrainedProfileTailWeight_le_intermediate
      hstart hstartCutoff hcutoffn pref profileUpperDelta 1
        (conditionalTailEnvelope n profileUpperTailStart) (by
          intro midPref hmidPref
          have hup :=
            ProfileConditionalTailUpper.constrainedProfileTailWeight_le_exp
              (n := n) (start := profileUpperTailStart) (le_refl _)
              hcutoffn midPref
          change 1 *
              ProfileConditionalTailUpper.constrainedProfileTailWeight
                n profileUpperTailStart
                  (by norm_num [profileUpperTailStart]) hcutoffn midPref
                    profileUpperDelta ≤
            Real.exp (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
              ProfileA11Assembly.a11ErrorCoefficient
                  profileUpperDelta 2 1 11 *
                (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
              ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ))
          simpa only [one_mul] using hup)
  have hone := constrainedProfileTailWeight_le_one hstart hstartCutoff
    pref profileUpperDelta hpref
  calc
    ProfileConditionalTailUpper.constrainedProfileTailWeight
        n start hstart (hstartCutoff.trans hcutoffn) pref
          profileUpperDelta =
        1 * ProfileConditionalTailUpper.constrainedProfileTailWeight
          n start hstart (hstartCutoff.trans hcutoffn) pref
            profileUpperDelta := by ring
    _ ≤ conditionalTailEnvelope n profileUpperTailStart *
        ProfileConditionalTailUpper.constrainedProfileTailWeight
          profileUpperTailStart start hstart hstartCutoff pref
            profileUpperDelta := hdis
    _ ≤ conditionalTailEnvelope n profileUpperTailStart * 1 :=
      mul_le_mul_of_nonneg_left hone
        (conditionalTailEnvelope_nonneg n profileUpperTailStart)
    _ = conditionalTailEnvelope n profileUpperTailStart := by ring

theorem endpointTailWeight_le_exp
    {n start a : ℕ}
    (htail : profileUpperTailStart ≤ start) (hstartn : start ≤ n)
    (ha : a ∈ allowedValues profileUpperDelta start) :
    endpointTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htail)
        hstartn a profileUpperDelta ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        ProfileA11Assembly.a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
        ∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
  rw [endpointTailWeight_eq_constrainedProfileTailWeight _ _ ha]
  exact ProfileConditionalTailUpper.constrainedProfileTailWeight_le_exp
    htail hstartn (endpointCenterProfile start a)

/-- Moving the A.11 starting point at most three scales past the cutoff
costs at most `exp 6`. -/
theorem conditionalTailEnvelope_le_exp_six_mul_cutoff
    {n start : ℕ} (hcutoffStart : profileUpperTailStart ≤ start)
    (hstartNear : start ≤ profileUpperTailStart + 3)
    (hstartn : start ≤ n) :
    conditionalTailEnvelope n start ≤
      Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart := by
  have hsubset : Finset.Ico start n ⊆
      Finset.Ico profileUpperTailStart n := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    exact ⟨hcutoffStart.trans hj.1, hj.2⟩
  have hsum :
      (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) ≤
        ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j _ _ ↦ by positivity)
  have hcutoffn : profileUpperTailStart ≤ n :=
    hcutoffStart.trans hstartn
  have hcastStart : ((n - start : ℕ) : ℝ) = (n : ℝ) - start := by
    rw [Nat.cast_sub hstartn]
  have hcastCutoff : ((n - profileUpperTailStart : ℕ) : ℝ) =
      (n : ℝ) - profileUpperTailStart := by
    rw [Nat.cast_sub hcutoffn]
  unfold conditionalTailEnvelope
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [hcastStart, hcastCutoff]
  have hnearReal : (start : ℝ) ≤ profileUpperTailStart + 3 := by
    exact_mod_cast hstartNear
  nlinarith

/-- For a four-step buffer beginning before the Taylor cutoff, every
allowed endpoint tail is bounded by the cutoff envelope with one fixed
`exp 6` loss. -/
theorem endpointTailWeight_le_smallEnvelope
    {n low a : ℕ} (hlow : 2 ≤ low)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n)
    (hstop : low + 4 ≤ n)
    (ha : a ∈ allowedValues profileUpperDelta (low + 4)) :
    endpointTailWeight n (low + 4) (by omega) hstop a
        profileUpperDelta ≤
      Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart := by
  by_cases hhighCutoff : low + 4 ≤ profileUpperTailStart
  · calc
      endpointTailWeight n (low + 4) (by omega) hstop a
          profileUpperDelta ≤
          conditionalTailEnvelope n profileUpperTailStart :=
        endpointTailWeight_le_envelope_from_cutoff
          (by omega) hhighCutoff hcutoffn ha
      _ ≤ Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart := by
        have hexp : (1 : ℝ) ≤ Real.exp 6 := Real.one_le_exp (by norm_num)
        nlinarith [conditionalTailEnvelope_nonneg
          n profileUpperTailStart]
  · have hcutoffHigh : profileUpperTailStart ≤ low + 4 := by omega
    have hhighNear : low + 4 ≤ profileUpperTailStart + 3 := by omega
    calc
      endpointTailWeight n (low + 4) (by omega) hstop a
          profileUpperDelta ≤ conditionalTailEnvelope n (low + 4) := by
        exact endpointTailWeight_le_exp hcutoffHigh hstop ha
      _ ≤ Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart :=
        conditionalTailEnvelope_le_exp_six_mul_cutoff
          hcutoffHigh hhighNear hstop

/-- Transition products agree when their state functions agree throughout
the segment, including both endpoints. -/
theorem transitionSegmentProduct_congr
    {start steps : ℕ} {f g : ℕ → ℕ}
    (hfg : ∀ j ≤ steps, f (start + j) = g (start + j)) :
    transitionSegmentProduct start steps f =
      transitionSegmentProduct start steps g := by
  rw [transitionSegmentProduct_eq_prod_Ico,
    transitionSegmentProduct_eq_prod_Ico]
  apply Finset.prod_congr rfl
  intro l hl
  have hl' := Finset.mem_Ico.mp hl
  have hleft : l = start + (l - start) := by omega
  have hright : l + 1 = start + (l + 1 - start) := by omega
  rw [hleft, hfg (l - start) (by omega)]
  have hedge : start + (l - start) + 1 =
      start + (l + 1 - start) := by omega
  rw [hedge, hfg (l + 1 - start) (by omega)]

/-- The tail component of the three-way profile split has precisely the
endpoint-tail transition product. -/
theorem endpointTailTerm_threeSplit
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (m : Profile n) :
    endpointTailTerm n (low + 4) (by omega) hstop
        ((profileThreeSplitEquiv hlow hstop m).2.1 ⟨3, by omega⟩)
        (profileThreeSplitEquiv hlow hstop m).2.2 =
      transitionSegmentProduct (low + 4) (n - (low + 4))
        (profileAtScale m) := by
  unfold endpointTailTerm
  apply transitionSegmentProduct_congr
  intro j hj
  by_cases hz : j = 0
  · subst j
    simp only [Nat.add_zero]
    rw [profileAtScale, dif_pos (by constructor <;> omega)]
    unfold extendProfile
    rw [dif_pos (by
      change low + 4 - 2 < low + 4 - 1
      omega)]
    unfold endpointCenterProfile
    rw [if_pos (by
      unfold scaleIndex
      change low + 4 - 2 + 2 = low + 4
      omega)]
    simpa only [profileThreeSplitEquiv_bridge_eq_profileAtScale,
      Nat.reduceAdd, Fin.isValue]
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hz
    let i : Fin (n - (low + 4)) := ⟨j - 1, by omega⟩
    have hscale : low + 4 + j = low + 4 + 1 + i.1 := by
      dsimp only [i]
      omega
    rw [hscale]
    rw [profileAtScale, dif_pos (by constructor <;> omega)]
    unfold extendProfile
    rw [dif_neg (by
      change ¬(low + 4 + 1 + i.1 - 2 < low + 4 - 1)
      omega)]
    have hindex :
        (⟨low + 4 + 1 + i.1 - 2 - (low + 4 - 1), by omega⟩ :
          Fin (n - (low + 4))) = i := by
      apply Fin.ext
      change low + 4 + 1 + i.1 - 2 - (low + 4 - 1) = i.1
      omega
    rw [hindex]
    exact profileThreeSplitEquiv_tail_eq_profileAtScale hlow hstop m i

/-- Exact factorization of the profile weight through the four-step local
bridge. -/
theorem profileWeight_eq_threeSplit
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (m : Profile n) :
    profileWeight m =
      profileWeight ((profileThreeSplitEquiv hlow hstop m).1) *
        transitionSegmentProduct low 4 (profileAtScale m) *
        transitionSegmentProduct (low + 4) (n - (low + 4))
          (profileAtScale m) := by
  rw [profileThreeSplitEquiv_fst]
  rw [ProfileConditionalTailUpper.profileWeight_eq_prefix_mul_tail
    hlow (by omega) m]
  have hsteps : n - low = 4 + (n - (low + 4)) := by omega
  rw [hsteps, transitionSegmentProduct_append]
  ring

/-- The exact erased-coordinate tilt and local transition product are
dominated by the literal four-step tilted path weight. -/
theorem erased_mul_local_le_tiltedPathWeight
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) (m : Profile n) :
    ENNReal.ofReal
        (r ^ erasedProfileSum low (low + 4) m *
          transitionSegmentProduct low 4 (profileAtScale m)) ≤
      tiltedPathWeightENNReal 4 r
        (profileAtScale ((profileThreeSplitEquiv hlow hstop m).1) low)
        (profileThreeSplitEquiv hlow hstop m).2.1 := by
  let path := (profileThreeSplitEquiv hlow hstop m).2.1
  have hr0 : 0 ≤ r := (by linarith : (0 : ℝ) ≤ r)
  have hsum : erasedProfileSum low (low + 4) m ≤ ∑ i, path i := by
    simpa only [path, profileThreeSplitEquiv_bridge_eq_profileAtScale] using
      erasedProfileSum_le_four_bridge_sum hlow hstop m
  have hpow : r ^ erasedProfileSum low (low + 4) m ≤
      r ^ (∑ i, path i) := by
    exact pow_le_pow_right₀ hr hsum
  have hlocal0 := transitionSegmentProduct_nonneg low 4 (profileAtScale m)
  have hreal :
      r ^ erasedProfileSum low (low + 4) m *
          transitionSegmentProduct low 4 (profileAtScale m) ≤
        r ^ (∑ i, path i) *
          transitionSegmentProduct low 4 (profileAtScale m) :=
    mul_le_mul_of_nonneg_right hpow hlocal0
  rw [tiltedPathWeightENNReal_eq_ofReal 4 r hr0]
  apply ENNReal.ofReal_le_ofReal hreal |>.trans_eq
  congr 2
  have hprefix :
      profileAtScale ((profileThreeSplitEquiv hlow hstop m).1) low =
        profileAtScale m low := by
    rw [profileThreeSplitEquiv_fst,
      profileAtScale_profilePrefix hlow (by omega)]
  rw [hprefix]
  have hpath : path =
      fun i : Fin 4 ↦ profileAtScale m (low + 1 + i.1) := by
    funext i
    exact profileThreeSplitEquiv_bridge_eq_profileAtScale hlow hstop m i
  change transitionSegmentProduct low 4 (profileAtScale m) =
    pathTransitionProduct 4 (profileAtScale m low) path
  rw [hpath, pathTransitionProduct_profile]

/-- The right endpoint of the four-step split is retained and constrained. -/
theorem threeSplit_bridgeLast_mem
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low (low + 4) delta m) :
    (profileThreeSplitEquiv hlow hstop m).2.1 ⟨3, by omega⟩ ∈
      allowedValues delta (low + 4) := by
  rw [profileThreeSplitEquiv_bridge_eq_profileAtScale]
  exact buffered_high_mem_allowedValues (by omega) hstop hm

/-- The tail component of the split is coordinatewise constrained. -/
theorem threeSplit_tail_mem
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low (low + 4) delta m) :
    (profileThreeSplitEquiv hlow hstop m).2.2 ∈
      Fintype.piFinset
        (fun i : Fin (n - (low + 4)) ↦
          allowedValues delta (low + 4 + 1 + i.1)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [profileThreeSplitEquiv_tail_eq_profileAtScale]
  rw [mem_allowedValues]
  let j : Fin (n - 1) := ⟨low + 4 + 1 + i.1 - 2, by
    have := i.2
    omega⟩
  have hscale : scaleIndex j = low + 4 + 1 + i.1 := by
    unfold scaleIndex
    dsimp only [j]
    omega
  have hj := hm j (Or.inr (by omega : low + 4 ≤ scaleIndex j))
  unfold InProfileWindow profileCenter
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hscale, profileAtScale_scaleIndex]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hj

/-- The constrained right-tail factor after a literal four-step bridge. -/
def separatedTailFactor
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (delta : ℝ) (path : Fin 4 → ℕ)
    (tail : Fin (n - (low + 4)) → ℕ) : ENNReal :=
  if path ⟨3, by omega⟩ ∈ allowedValues delta (low + 4) then
      if tail ∈ Fintype.piFinset
          (fun i : Fin (n - (low + 4)) ↦
            allowedValues delta (low + 4 + 1 + i.1)) then
        ENNReal.ofReal
          (endpointTailTerm n (low + 4) (by omega) hstop
            (path ⟨3, by omega⟩) tail)
      else 0
    else 0

/-- Product majorant on the prefix/bridge/tail coordinates. -/
def separatedProfileMajorant
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (r delta : ℝ)
    (p : Profile low ×
      ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ))) : ENNReal :=
  (if p.1 ∈ constrainedProfiles low delta then
      ENNReal.ofReal (profileWeight p.1) else 0) *
    tiltedPathWeightENNReal 4 r (profileAtScale p.1 low) p.2.1 *
    separatedTailFactor hlow hstop delta p.2.1 p.2.2

/-- Every buffered tilted profile summand is bounded by its split-coordinate
majorant. -/
theorem buffered_summand_le_separatedProfileMajorant
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    {r : ℝ} (hr : 1 ≤ r) {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low (low + 4) delta m) :
    ENNReal.ofReal
        (r ^ erasedProfileSum low (low + 4) m * profileWeight m) ≤
      separatedProfileMajorant hlow hstop r delta
        (profileThreeSplitEquiv hlow hstop m) := by
  let pref := (profileThreeSplitEquiv hlow hstop m).1
  let path := (profileThreeSplitEquiv hlow hstop m).2.1
  let tail := (profileThreeSplitEquiv hlow hstop m).2.2
  have hpref : pref ∈ constrainedProfiles low delta := by
    dsimp only [pref]
    rw [profileThreeSplitEquiv_fst]
    exact buffered_profilePrefix_mem hlow (by omega) hm
  have hend : path ⟨3, by omega⟩ ∈
      allowedValues delta (low + 4) :=
    threeSplit_bridgeLast_mem hlow hstop hm
  have htail : tail ∈ Fintype.piFinset
      (fun i : Fin (n - (low + 4)) ↦
        allowedValues delta (low + 4 + 1 + i.1)) :=
    threeSplit_tail_mem hlow hstop hm
  have hpref0 : 0 ≤ profileWeight pref := profileWeight_nonneg pref
  have hlocal0 := transitionSegmentProduct_nonneg low 4 (profileAtScale m)
  have htail0 := transitionSegmentProduct_nonneg
    (low + 4) (n - (low + 4)) (profileAtScale m)
  rw [profileWeight_eq_threeSplit hlow hstop m]
  change ENNReal.ofReal
      (r ^ erasedProfileSum low (low + 4) m *
        (profileWeight pref *
          transitionSegmentProduct low 4 (profileAtScale m) *
          transitionSegmentProduct (low + 4) (n - (low + 4))
            (profileAtScale m))) ≤ _
  rw [show r ^ erasedProfileSum low (low + 4) m *
        (profileWeight pref *
          transitionSegmentProduct low 4 (profileAtScale m) *
          transitionSegmentProduct (low + 4) (n - (low + 4))
            (profileAtScale m)) =
      profileWeight pref *
        (r ^ erasedProfileSum low (low + 4) m *
          transitionSegmentProduct low 4 (profileAtScale m)) *
        transitionSegmentProduct (low + 4) (n - (low + 4))
          (profileAtScale m) by ring]
  have htiltedLocal0 : 0 ≤
      r ^ erasedProfileSum low (low + 4) m *
        transitionSegmentProduct low 4 (profileAtScale m) :=
    mul_nonneg (pow_nonneg (by linarith) _) hlocal0
  rw [ENNReal.ofReal_mul (mul_nonneg hpref0 htiltedLocal0),
    ENNReal.ofReal_mul hpref0]
  unfold separatedProfileMajorant separatedTailFactor
  rw [if_pos hpref, if_pos hend, if_pos htail]
  change ENNReal.ofReal (profileWeight pref) *
        ENNReal.ofReal
          (r ^ erasedProfileSum low (low + 4) m *
            transitionSegmentProduct low 4 (profileAtScale m)) *
        ENNReal.ofReal
          (transitionSegmentProduct (low + 4) (n - (low + 4))
            (profileAtScale m)) ≤
      ENNReal.ofReal (profileWeight pref) *
        tiltedPathWeightENNReal 4 r (profileAtScale pref low) path *
        ENNReal.ofReal
          (endpointTailTerm n (low + 4) (by omega) hstop
            (path ⟨3, by omega⟩) tail)
  gcongr
  · exact erased_mul_local_le_tiltedPathWeight hlow hstop hr m
  · rw [endpointTailTerm_threeSplit hlow hstop m]

private theorem tsum_indicator_tail_eq_endpointTailWeight_early
    {n start a : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (delta : ℝ) :
    (∑' future : Fin (n - start) → ℕ,
      if future ∈ Fintype.piFinset
          (fun i : Fin (n - start) ↦
            allowedValues delta (start + 1 + i.1)) then
        ENNReal.ofReal
          (endpointTailTerm n start hstart hstartn a future)
      else 0) =
        ENNReal.ofReal
          (endpointTailWeight n start hstart hstartn a delta) := by
  let F := Fintype.piFinset
    (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  rw [tsum_eq_sum (s := F)]
  · have hsum :
        (∑ future ∈ F,
          if future ∈ Fintype.piFinset
              (fun i : Fin (n - start) ↦
                allowedValues delta (start + 1 + i.1)) then
            ENNReal.ofReal
              (endpointTailTerm n start hstart hstartn a future)
          else 0) =
        ∑ future ∈ F,
          ENNReal.ofReal
            (endpointTailTerm n start hstart hstartn a future) := by
        apply Finset.sum_congr rfl
        intro future hfuture
        rw [if_pos hfuture]
    rw [hsum]
    unfold endpointTailWeight endpointTailTerm
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro future _
    exact transitionSegmentProduct_nonneg start (n - start) _
  · intro future hfuture
    rw [if_neg hfuture]

/-- The right-tail sum for a buffer beginning before the Taylor cutoff. -/
theorem tsum_separatedTailFactor_le_small
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) (path : Fin 4 → ℕ) :
    (∑' tail : Fin (n - (low + 4)) → ℕ,
      separatedTailFactor hlow hstop profileUpperDelta path tail) ≤
        ENNReal.ofReal
          (Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart) := by
  by_cases hend : path ⟨3, by omega⟩ ∈
      allowedValues profileUpperDelta (low + 4)
  · have hfun :
        (fun tail : Fin (n - (low + 4)) → ℕ ↦
          separatedTailFactor hlow hstop profileUpperDelta path tail) =
        fun tail ↦
          if tail ∈ Fintype.piFinset
              (fun i : Fin (n - (low + 4)) ↦
                allowedValues profileUpperDelta (low + 4 + 1 + i.1)) then
            ENNReal.ofReal
              (endpointTailTerm n (low + 4) (by omega) hstop
                (path ⟨3, by omega⟩) tail)
          else 0 := by
      funext tail
      simp only [separatedTailFactor, if_pos hend]
    rw [hfun, tsum_indicator_tail_eq_endpointTailWeight_early]
    exact ENNReal.ofReal_le_ofReal
      (endpointTailWeight_le_smallEnvelope hlow hlowCutoff hcutoffn
        hstop hend)
  · have hfun :
        (fun tail : Fin (n - (low + 4)) → ℕ ↦
          separatedTailFactor hlow hstop profileUpperDelta path tail) =
          fun _ ↦ 0 := by
      funext tail
      simp only [separatedTailFactor, if_neg hend]
    rw [hfun]
    simp

/-- Summing all allowed right tails after one bridge costs at most the
uniform conditional A.11 envelope. -/
theorem tsum_separatedTailFactor_le
    {n low : ℕ} (hlow : 2 ≤ low) (hstop : low + 4 ≤ n)
    (htail : profileUpperTailStart ≤ low) (path : Fin 4 → ℕ) :
    (∑' tail : Fin (n - (low + 4)) → ℕ,
      separatedTailFactor hlow hstop profileUpperDelta path tail) ≤
        ENNReal.ofReal (conditionalTailEnvelope n (low + 4)) := by
  by_cases hend : path ⟨3, by omega⟩ ∈
      allowedValues profileUpperDelta (low + 4)
  · have hfun :
        (fun tail : Fin (n - (low + 4)) → ℕ ↦
          separatedTailFactor hlow hstop profileUpperDelta path tail) =
        fun tail ↦
          if tail ∈ Fintype.piFinset
              (fun i : Fin (n - (low + 4)) ↦
                allowedValues profileUpperDelta (low + 4 + 1 + i.1)) then
            ENNReal.ofReal
              (endpointTailTerm n (low + 4) (by omega) hstop
                (path ⟨3, by omega⟩) tail)
          else 0 := by
      funext tail
      simp only [separatedTailFactor, if_pos hend]
    rw [hfun]
    rw [tsum_indicator_tail_eq_endpointTailWeight_early]
    exact ENNReal.ofReal_le_ofReal
      (endpointTailWeight_le_exp (htail.trans (by omega)) hstop hend)
  · have hfun :
        (fun tail : Fin (n - (low + 4)) → ℕ ↦
          separatedTailFactor hlow hstop profileUpperDelta path tail) =
          fun _ ↦ 0 := by
      funext tail
      simp only [separatedTailFactor, if_neg hend]
    rw [hfun]
    simp

/-- The tilted four-step bridge followed by all constrained right tails has
one fixed total cost. -/
theorem tsum_bridge_mul_tail_le
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) (htail : profileUpperTailStart ≤ low)
    (pref : Profile low)
    (hpref : pref ∈ constrainedProfiles low profileUpperDelta) :
    (∑' p : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
      tiltedPathWeightENNReal 4
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
          (profileAtScale pref low) p.1 *
        separatedTailFactor hlow hstop profileUpperDelta p.1 p.2) ≤
      ENNReal.ofReal (Real.exp 360) *
        ENNReal.ofReal (conditionalTailEnvelope n (low + 4)) := by
  have hprefC : IsConstrainedProfile profileUpperDelta pref :=
    mem_constrainedProfiles.mp hpref
  let i : Fin (low - 1) := ⟨low - 2, by omega⟩
  have haNat : pref i ≤ 3 * low ^ 2 :=
    AnnularIntegratedProfileKernel.constrainedProfile_entry_le_three_mul_n_sq
      (by norm_num [profileUpperDelta]) hprefC i
  have haScale : profileAtScale pref low = pref i := by
    unfold profileAtScale
    rw [dif_pos ⟨hlow, le_rfl⟩]
  have ha : (profileAtScale pref low : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
    rw [haScale]
    have hlowN : low ≤ n := by omega
    have hnat : pref i ≤ 3 * n ^ 2 :=
      haNat.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hlowN 2))
    exact_mod_cast hnat
  change (∑' p : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
      (fun path tail ↦
        tiltedPathWeightENNReal 4
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
            (profileAtScale pref low) path *
          separatedTailFactor hlow hstop profileUpperDelta path tail)
        p.1 p.2) ≤ _
  have hprod := @ENNReal.tsum_prod
    (Fin 4 → ℕ) (Fin (n - (low + 4)) → ℕ)
    (fun path tail ↦
      tiltedPathWeightENNReal 4
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
          (profileAtScale pref low) path *
        separatedTailFactor hlow hstop profileUpperDelta path tail)
  rw [hprod]
  calc
    (∑' path : Fin 4 → ℕ,
        ∑' tail : Fin (n - (low + 4)) → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            separatedTailFactor hlow hstop profileUpperDelta path tail) =
        ∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            (∑' tail : Fin (n - (low + 4)) → ℕ,
              separatedTailFactor hlow hstop profileUpperDelta path tail) := by
      apply tsum_congr
      intro path
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            ENNReal.ofReal (conditionalTailEnvelope n (low + 4)) := by
      apply ENNReal.tsum_le_tsum
      intro path
      exact mul_le_mul' (le_refl _)
        (tsum_separatedTailFactor_le hlow hstop htail path)
    _ = (∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
            (profileAtScale pref low) path) *
          ENNReal.ofReal (conditionalTailEnvelope n (low + 4)) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal (conditionalTailEnvelope n (low + 4)) := by
      exact mul_le_mul'
        (tsum_tiltedPathWeightENNReal_exactCutoff_le_exp_threeSixty
          (steps := 4) hn (by norm_num) ha) (le_refl _)

/-- The same tilted bridge estimate when the buffer begins before the
Taylor cutoff. -/
theorem tsum_bridge_mul_tail_le_small
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n)
    (pref : Profile low)
    (hpref : pref ∈ constrainedProfiles low profileUpperDelta) :
    (∑' p : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
      tiltedPathWeightENNReal 4
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
          (profileAtScale pref low) p.1 *
        separatedTailFactor hlow hstop profileUpperDelta p.1 p.2) ≤
      ENNReal.ofReal (Real.exp 360) *
        ENNReal.ofReal
          (Real.exp 6 * conditionalTailEnvelope n profileUpperTailStart) := by
  have hprefC : IsConstrainedProfile profileUpperDelta pref :=
    mem_constrainedProfiles.mp hpref
  let i : Fin (low - 1) := ⟨low - 2, by omega⟩
  have haNat : pref i ≤ 3 * low ^ 2 :=
    AnnularIntegratedProfileKernel.constrainedProfile_entry_le_three_mul_n_sq
      (by norm_num [profileUpperDelta]) hprefC i
  have haScale : profileAtScale pref low = pref i := by
    unfold profileAtScale
    rw [dif_pos ⟨hlow, le_rfl⟩]
  have ha : (profileAtScale pref low : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by
    rw [haScale]
    have hlowN : low ≤ n := by omega
    have hnat : pref i ≤ 3 * n ^ 2 :=
      haNat.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hlowN 2))
    exact_mod_cast hnat
  change (∑' p : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
      (fun path tail ↦
        tiltedPathWeightENNReal 4
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
            (profileAtScale pref low) path *
          separatedTailFactor hlow hstop profileUpperDelta path tail)
        p.1 p.2) ≤ _
  have hprod := @ENNReal.tsum_prod
    (Fin 4 → ℕ) (Fin (n - (low + 4)) → ℕ)
    (fun path tail ↦
      tiltedPathWeightENNReal 4
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
          (profileAtScale pref low) path *
        separatedTailFactor hlow hstop profileUpperDelta path tail)
  rw [hprod]
  calc
    (∑' path : Fin 4 → ℕ,
        ∑' tail : Fin (n - (low + 4)) → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            separatedTailFactor hlow hstop profileUpperDelta path tail) =
        ∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            (∑' tail : Fin (n - (low + 4)) → ℕ,
              separatedTailFactor hlow hstop profileUpperDelta path tail) := by
      apply tsum_congr
      intro path
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
              ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
              (profileAtScale pref low) path *
            ENNReal.ofReal
              (Real.exp 6 *
                conditionalTailEnvelope n profileUpperTailStart) := by
      apply ENNReal.tsum_le_tsum
      intro path
      exact mul_le_mul' (le_refl _)
        (tsum_separatedTailFactor_le_small hlow hstop hlowCutoff
          hcutoffn path)
    _ = (∑' path : Fin 4 → ℕ,
          tiltedPathWeightENNReal 4
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2)
            (profileAtScale pref low) path) *
          ENNReal.ofReal
            (Real.exp 6 *
              conditionalTailEnvelope n profileUpperTailStart) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal
            (Real.exp 6 *
              conditionalTailEnvelope n profileUpperTailStart) := by
      exact mul_le_mul'
        (tsum_tiltedPathWeightENNReal_exactCutoff_le_exp_threeSixty
          (steps := 4) hn (by norm_num) ha) (le_refl _)

/-- The finite constrained-prefix indicator sums to the ordinary profile
weight. -/
theorem tsum_constrainedProfile_indicator_eq
    (n : ℕ) (delta : ℝ) :
    (∑' m : Profile n,
      if m ∈ constrainedProfiles n delta then
        ENNReal.ofReal (profileWeight m) else 0) =
      ENNReal.ofReal (constrainedProfileWeight n delta) := by
  rw [tsum_eq_sum (s := constrainedProfiles n delta)]
  · have hsum :
        (∑ m ∈ constrainedProfiles n delta,
          if m ∈ constrainedProfiles n delta then
            ENNReal.ofReal (profileWeight m) else 0) =
          ∑ m ∈ constrainedProfiles n delta,
            ENNReal.ofReal (profileWeight m) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [if_pos hm]
    rw [hsum]
    unfold constrainedProfileWeight
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro m _
    exact profileWeight_nonneg m
  · intro m hm
    rw [if_neg hm]

/-- Including the omitted transition from the forced scale-one count turns
the entire finite prefix into a genuine Markov path weight. -/
theorem firstProfileTransitionMass_mul_profileWeight_eq_path
    {low : ℕ} (hlow : 2 ≤ low) (pref : Profile low) :
    firstProfileTransitionMass hlow pref * profileWeight pref =
      pathTransitionProduct (low - 1) 1 pref := by
  unfold firstProfileTransitionMass profileWeight profileList
  exact transitionMass_mul_transitionProduct_ofFn_eq_path
    (by omega) pref

/-- The constrained prefix mass is uniformly bounded even before the
Taylor cutoff.  The factor `8192` is the reciprocal of the checked first
transition lower bound. -/
theorem constrainedProfileWeight_le_8192
    {low : ℕ} (hlow : 2 ≤ low) :
    constrainedProfileWeight low profileUpperDelta ≤ 8192 := by
  rw [← ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 8192)]
  unfold constrainedProfileWeight
  rw [ENNReal.ofReal_sum_of_nonneg]
  · calc
      (∑ pref ∈ constrainedProfiles low profileUpperDelta,
          ENNReal.ofReal (profileWeight pref)) ≤
          ∑ pref ∈ constrainedProfiles low profileUpperDelta,
            ENNReal.ofReal 8192 *
              ENNReal.ofReal
                (firstProfileTransitionMass hlow pref *
                  profileWeight pref) := by
        apply Finset.sum_le_sum
        intro pref hpref
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8192)]
        apply ENNReal.ofReal_le_ofReal
        have hfirst := one_div_8192_le_firstProfileTransitionMass
          hlow (by norm_num [profileUpperDelta])
            (mem_constrainedProfiles.mp hpref)
        have hweight := profileWeight_nonneg pref
        nlinarith [mul_nonneg
          (show 0 ≤ firstProfileTransitionMass hlow pref by
            unfold firstProfileTransitionMass
            exact transitionMass_nonneg _ _)
          hweight]
      _ = ENNReal.ofReal 8192 *
          (∑ pref ∈ constrainedProfiles low profileUpperDelta,
            ENNReal.ofReal
              (firstProfileTransitionMass hlow pref *
                profileWeight pref)) := by
        rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal 8192 *
          (∑' pref : Profile low,
            ENNReal.ofReal
              (firstProfileTransitionMass hlow pref *
                profileWeight pref)) := by
        exact mul_le_mul' (le_refl _)
          (ENNReal.summable.sum_le_tsum _ (fun _ _ ↦ bot_le))
      _ = ENNReal.ofReal 8192 * 1 := by
        congr 1
        calc
          (∑' pref : Profile low,
              ENNReal.ofReal
                (firstProfileTransitionMass hlow pref *
                  profileWeight pref)) =
              ∑' pref : Fin (low - 1) → ℕ,
                ENNReal.ofReal
                  (pathTransitionProduct (low - 1) 1 pref) := by
            apply tsum_congr
            intro pref
            rw [firstProfileTransitionMass_mul_profileWeight_eq_path hlow]
          _ = 1 := tsum_pathTransitionProduct_eq_one (low - 1) 1
      _ = ENNReal.ofReal 8192 := by simp
  · intro pref _hpref
    exact profileWeight_nonneg pref

/-- Total mass of the split majorant: constrained prefix, tilted bridge,
and constrained conditional tail. -/
theorem tsum_separatedProfileMajorant_le
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) (htail : profileUpperTailStart ≤ low) :
    (∑' p : Profile low ×
        ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
      separatedProfileMajorant hlow hstop
        ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p) ≤
      ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
        (ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal (conditionalTailEnvelope n (low + 4))) := by
  change (∑' p : Profile low ×
      ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
    (fun pref pt ↦ separatedProfileMajorant hlow hstop
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (pref, pt))
      p.1 p.2) ≤ _
  have hprod := @ENNReal.tsum_prod
    (Profile low)
    ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ))
    (fun pref pt ↦ separatedProfileMajorant hlow hstop
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (pref, pt))
  rw [hprod]
  calc
    (∑' pref : Profile low,
        ∑' pt : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
          separatedProfileMajorant hlow hstop
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta
            (pref, pt)) ≤
      ∑' pref : Profile low,
        (if pref ∈ constrainedProfiles low profileUpperDelta then
          ENNReal.ofReal (profileWeight pref) else 0) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal (conditionalTailEnvelope n (low + 4))) := by
      apply ENNReal.tsum_le_tsum
      intro pref
      unfold separatedProfileMajorant
      simp only [Prod.fst, Prod.snd]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left]
      by_cases hpref : pref ∈ constrainedProfiles low profileUpperDelta
      · rw [if_pos hpref]
        exact mul_le_mul' (le_refl _)
          (tsum_bridge_mul_tail_le hn hlow hstop htail pref hpref)
      · rw [if_neg hpref, zero_mul]
        exact bot_le
    _ = (∑' pref : Profile low,
          if pref ∈ constrainedProfiles low profileUpperDelta then
            ENNReal.ofReal (profileWeight pref) else 0) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal (conditionalTailEnvelope n (low + 4))) := by
      rw [ENNReal.tsum_mul_right]
    _ = _ := by
      rw [tsum_constrainedProfile_indicator_eq]

/-- Total mass of the split majorant before the Taylor cutoff. -/
theorem tsum_separatedProfileMajorant_le_small
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' p : Profile low ×
        ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
      separatedProfileMajorant hlow hstop
        ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p) ≤
      ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
        (ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal
            (Real.exp 6 *
              conditionalTailEnvelope n profileUpperTailStart)) := by
  change (∑' p : Profile low ×
      ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
    (fun pref pt ↦ separatedProfileMajorant hlow hstop
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (pref, pt))
      p.1 p.2) ≤ _
  have hprod := @ENNReal.tsum_prod
    (Profile low)
    ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ))
    (fun pref pt ↦ separatedProfileMajorant hlow hstop
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (pref, pt))
  rw [hprod]
  calc
    (∑' pref : Profile low,
        ∑' pt : (Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ),
          separatedProfileMajorant hlow hstop
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta
            (pref, pt)) ≤
      ∑' pref : Profile low,
        (if pref ∈ constrainedProfiles low profileUpperDelta then
          ENNReal.ofReal (profileWeight pref) else 0) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal
              (Real.exp 6 *
                conditionalTailEnvelope n profileUpperTailStart)) := by
      apply ENNReal.tsum_le_tsum
      intro pref
      unfold separatedProfileMajorant
      simp only [Prod.fst, Prod.snd]
      simp_rw [mul_assoc]
      rw [ENNReal.tsum_mul_left]
      by_cases hpref : pref ∈ constrainedProfiles low profileUpperDelta
      · rw [if_pos hpref]
        exact mul_le_mul' (le_refl _)
          (tsum_bridge_mul_tail_le_small hn hlow hstop hlowCutoff
            hcutoffn pref hpref)
      · rw [if_neg hpref, zero_mul]
        exact bot_le
    _ = (∑' pref : Profile low,
          if pref ∈ constrainedProfiles low profileUpperDelta then
            ENNReal.ofReal (profileWeight pref) else 0) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal
              (Real.exp 6 *
                conditionalTailEnvelope n profileUpperTailStart)) := by
      rw [ENNReal.tsum_mul_right]
    _ = _ := by
      rw [tsum_constrainedProfile_indicator_eq]

/-- Reindex the actual buffered subtype into the split coordinates and sum
its tilted profile weights. -/
theorem tsum_buffered_tiltedProfileWeight_le
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) (htail : profileUpperTailStart ≤ low) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
            erasedProfileSum low (low + 4) m.1 *
          profileWeight m.1)) ≤
      ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
        (ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal (conditionalTailEnvelope n (low + 4))) := by
  let e := profileThreeSplitEquiv hlow hstop
  let split : {m : Profile n //
      IsBufferedInternalProfile low (low + 4) profileUpperDelta m} →
      Profile low ×
        ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)) :=
    fun m ↦ e m.1
  have hsplit : Function.Injective split := by
    intro left right hlr
    apply Subtype.ext
    exact e.injective hlr
  have hr : (1 : ℝ) ≤ (1 + 1 / (n : ℝ) ^ 4) ^ 2 := by
    have heps : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
    nlinarith [sq_nonneg (1 / (n : ℝ) ^ 4)]
  calc
    (∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        ENNReal.ofReal
          (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
              erasedProfileSum low (low + 4) m.1 *
            profileWeight m.1)) ≤
      ∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        separatedProfileMajorant hlow hstop
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (split m) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        buffered_summand_le_separatedProfileMajorant hlow hstop hr m.2
    _ ≤ ∑' p : Profile low ×
          ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
        separatedProfileMajorant hlow hstop
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p :=
      ENNReal.tsum_comp_le_tsum_of_injective hsplit _
    _ ≤ _ := tsum_separatedProfileMajorant_le hn hlow hstop htail

/-- Reindexing and summing the buffered tilted weights before the Taylor
cutoff. -/
theorem tsum_buffered_tiltedProfileWeight_le_small
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
            erasedProfileSum low (low + 4) m.1 *
          profileWeight m.1)) ≤
      ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
        (ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal
            (Real.exp 6 *
              conditionalTailEnvelope n profileUpperTailStart)) := by
  let e := profileThreeSplitEquiv hlow hstop
  let split : {m : Profile n //
      IsBufferedInternalProfile low (low + 4) profileUpperDelta m} →
      Profile low ×
        ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)) :=
    fun m ↦ e m.1
  have hsplit : Function.Injective split := by
    intro left right hlr
    apply Subtype.ext
    exact e.injective hlr
  have hr : (1 : ℝ) ≤ (1 + 1 / (n : ℝ) ^ 4) ^ 2 := by
    have heps : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
    nlinarith [sq_nonneg (1 / (n : ℝ) ^ 4)]
  calc
    (∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        ENNReal.ofReal
          (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
              erasedProfileSum low (low + 4) m.1 *
            profileWeight m.1)) ≤
      ∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        separatedProfileMajorant hlow hstop
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (split m) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        buffered_summand_le_separatedProfileMajorant hlow hstop hr m.2
    _ ≤ ∑' p : Profile low ×
          ((Fin 4 → ℕ) × (Fin (n - (low + 4)) → ℕ)),
        separatedProfileMajorant hlow hstop
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p :=
      ENNReal.tsum_comp_le_tsum_of_injective hsplit _
    _ ≤ _ := tsum_separatedProfileMajorant_le_small hn hlow hstop
      hlowCutoff hcutoffn

/-- The terminal negative-binomial window remains a subprobability because
the retained terminal profile count is positive. -/
theorem terminalWindowMass_le_one_of_buffered
    {n low high : ℕ} (hn : 2 ≤ n) (hhighn : high ≤ n)
    {delta : ℝ} (hdelta : delta ≤ 1) {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    TerminalNegativeBinomialWindow.terminalWindowMass n delta
        (TerminalNegativeBinomialWindow.terminalProfileCount hn m) ≤ 1 := by
  let i : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hwindowRaw := hm i (Or.inr (by
    have hscale : scaleIndex i = n := by
      unfold scaleIndex
      dsimp only [i]
      omega
    omega))
  have hwindow : InProfileWindow delta n (m i) := by
    unfold InProfileWindow profileCenter
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hscale : scaleIndex i = n := by
      unfold scaleIndex
      dsimp only [i]
      omega
    simpa only [hscale] using hwindowRaw
  have htwo := AnnularIntegratedProfileKernel.inProfileWindow_le_three_mul_sq
    hdelta (show 1 ≤ n by omega) hwindow
  have hi : 0 < TerminalNegativeBinomialWindow.terminalProfileCount hn m := by
    unfold TerminalNegativeBinomialWindow.terminalProfileCount
    change 0 < m i
    have hcenterLower : (1 : ℝ) ≤ m i := by
      rw [InProfileWindow, abs_le] at hwindow
      have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      dsimp only [profileCenter] at hwindow
      push_cast at hwindow
      have hpow : (n : ℝ) ^ (1 + delta) ≤ (n : ℝ) ^ 2 := by
        rw [← Real.rpow_two]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      nlinarith
    exact_mod_cast hcenterLower
  have hsummable := NegativeBinomial.summable_mass
    (ExcursionTransition.terminalSuccess_pos hn)
    (ExcursionTransition.terminalSuccess_le_one hn) hi
  unfold TerminalNegativeBinomialWindow.terminalWindowMass
  calc
    (∑ j ∈ Finset.Icc
          ⌈ThickPoint.terminalLower n delta⌉₊ (n ^ 3),
        NegativeBinomial.mass
          (ExcursionTransition.terminalSuccess n)
          (TerminalNegativeBinomialWindow.terminalProfileCount hn m) j) ≤
      ∑' j, NegativeBinomial.mass
        (ExcursionTransition.terminalSuccess n)
        (TerminalNegativeBinomialWindow.terminalProfileCount hn m) j :=
      hsummable.sum_le_tsum _ (fun j _ ↦ NegativeBinomial.mass_nonneg
        (ExcursionTransition.terminalSuccess_pos hn).le
        (ExcursionTransition.terminalSuccess_le_one hn) _ j)
    _ = 1 := NegativeBinomial.tsum_mass
      (ExcursionTransition.terminalSuccess_pos hn)
      (ExcursionTransition.terminalSuccess_le_one hn) hi

/-- One exact chronological radial-word profile cost is bounded by the
retained cutoff constant times its tilted profile weight. -/
theorem exactProfileCost_le_exp_nine_mul_tilted
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) {m : Profile n}
    (hm : IsBufferedInternalProfile low (low + 4) profileUpperDelta m) :
    ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m *
          (firstProfileTransitionMass (by omega) m *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m) *
            profileWeight m)) ≤
      ENNReal.ofReal (Real.exp 9) *
        ENNReal.ofReal
          (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
              erasedProfileSum low (low + 4) m * profileWeight m) := by
  let retained : ℝ :=
    (1 + 1 / (n : ℝ) ^ 4) ^
      (2 * (retainedProfileSum low (low + 4) m + n ^ 3) + 1)
  let r : ℝ := (1 + 1 / (n : ℝ) ^ 4) ^ 2
  let erased : ℝ := r ^ erasedProfileSum low (low + 4) m
  let first : ℝ := firstProfileTransitionMass (by omega) m
  let terminal : ℝ :=
    TerminalNegativeBinomialWindow.terminalWindowMass
      n profileUpperDelta
        (TerminalNegativeBinomialWindow.terminalProfileCount (by omega) m)
  have hretained : retained ≤ Real.exp 9 := by
    exact retained_exactCutoffFactor_le_exp_nine hn
      (by norm_num [profileUpperDelta]) hm
  have hfirst : first ≤ 1 := by
    exact transitionMass_le_one 1 (m ⟨0, by omega⟩)
  have hterminal : terminal ≤ 1 := by
    exact terminalWindowMass_le_one_of_buffered (by omega) hstop
      (by norm_num [profileUpperDelta]) hm
  have hretained0 : 0 ≤ retained := by dsimp [retained]; positivity
  have herased0 : 0 ≤ erased := by dsimp [erased, r]; positivity
  have hfirst0 : 0 ≤ first := by
    dsimp [first, firstProfileTransitionMass]
    exact transitionMass_nonneg _ _
  have hterminal0 : 0 ≤ terminal := by
    dsimp [terminal]
    exact TerminalNegativeBinomialWindow.terminalWindowMass_nonneg
      n profileUpperDelta _
        (ExcursionTransition.terminalSuccess_pos (by omega)).le
        (ExcursionTransition.terminalSuccess_le_one (by omega))
  have hweight0 := profileWeight_nonneg m
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 9)]
  apply ENNReal.ofReal_le_ofReal
  rw [exactCutoffFactor_eq_retained_mul_erased
    (low := low) (high := low + 4) m]
  change retained * erased * (first * terminal * profileWeight m) ≤
    Real.exp 9 * (erased * profileWeight m)
  calc
    retained * erased * (first * terminal * profileWeight m) ≤
        Real.exp 9 * erased * (1 * 1 * profileWeight m) := by
      gcongr
    _ = Real.exp 9 * (erased * profileWeight m) := by ring

/-- Summed exact radial-word cost for a buffer beginning before the Taylor
cutoff. -/
theorem tsum_buffered_exactProfileCost_le_small
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (by omega) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal (Real.exp 9) *
        (ENNReal.ofReal 8192 *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal
              (Real.exp 6 *
                conditionalTailEnvelope n profileUpperTailStart))) := by
  calc
    _ ≤ ∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        ENNReal.ofReal (Real.exp 9) *
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low (low + 4) m.1 *
              profileWeight m.1) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        exactProfileCost_le_exp_nine_mul_tilted hn hlow hstop m.2
    _ = ENNReal.ofReal (Real.exp 9) *
        (∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low (low + 4) m.1 *
              profileWeight m.1)) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (Real.exp 9) *
        (ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal
              (Real.exp 6 *
                conditionalTailEnvelope n profileUpperTailStart))) := by
      exact mul_le_mul' (le_refl _)
        (tsum_buffered_tiltedProfileWeight_le_small hn hlow hstop
          hlowCutoff hcutoffn)
    _ ≤ _ := by
      gcongr
      exact constrainedProfileWeight_le_8192 hlow

/-- The public one-point envelope absorbs the complete pre-cutoff buffered
cost. -/
theorem tsum_buffered_exactProfileCost_le_exp_small
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n)
    (hlowCutoff : low < profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (by omega) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  have hraw := tsum_buffered_exactProfileCost_le_small hn hlow hstop
    hlowCutoff hcutoffn
  have h8192 : (8192 : ℝ) ≤ Real.exp 10 := by
    have h27 : (2.7 : ℝ) < Real.exp 1 :=
      (by norm_num : (2.7 : ℝ) < 2.7182818283).trans
        Real.exp_one_gt_d9
    calc
      (8192 : ℝ) ≤ (2.7 : ℝ) ^ 10 := by norm_num
      _ ≤ Real.exp 1 ^ 10 :=
        (pow_lt_pow_left₀ h27 (by norm_num)
          (by norm_num)).le
      _ = Real.exp 10 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnPowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow hnOne (by norm_num)
  have hharm :
      (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
        3 * (n : ℝ) ^ (3 / 5 : ℝ) :=
    (harmonicTail_le_three_rpow (show 1 ≤ n by omega))
  have ha11 : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
      profileUpperDelta 2 1 11 :=
    ProfileA11Assembly.a11ErrorCoefficient_nonneg
      (by norm_num [profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.log
      ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      (constrainedProfiles profileUpperTailStart
        profileUpperDelta).card + 1 ≠ 0)
  have hcoef :
      ProfileA11Assembly.a11ErrorCoefficient
          profileUpperDelta 2 1 11 +
        2 * (profileUpperTailStart : ℝ) + 392 ≤
          profileUpperConstant := by
    unfold profileUpperConstant profileUpperCoreConstant
    push_cast
    nlinarith
  have hcast : ((n - profileUpperTailStart : ℕ) : ℝ) =
      (n : ℝ) - profileUpperTailStart := by
    rw [Nat.cast_sub hcutoffn]
  have hexponent :
      9 + 10 + 360 + 6 +
          (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            ProfileA11Assembly.a11ErrorCoefficient
                profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
            ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
        -(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) := by
    have hdelta : 3 * profileUpperDelta = (3 / 5 : ℝ) := by
      norm_num [profileUpperDelta]
    rw [hcast, hdelta]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith [mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ))]
  apply hraw.trans
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 360)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8192)]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 9)]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp 9 *
        (8192 * (Real.exp 360 *
          (Real.exp 6 *
            conditionalTailEnvelope n profileUpperTailStart))) ≤
      Real.exp 9 *
        (Real.exp 10 * (Real.exp 360 *
          (Real.exp 6 *
            conditionalTailEnvelope n profileUpperTailStart))) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg 9)
      apply mul_le_mul_of_nonneg_right h8192
      exact mul_nonneg (Real.exp_nonneg 360)
        (mul_nonneg (Real.exp_nonneg 6)
          (conditionalTailEnvelope_nonneg n profileUpperTailStart))
    _ = Real.exp
        (9 + 10 + 360 + 6 +
          (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            ProfileA11Assembly.a11ErrorCoefficient
                profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
            ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ))) := by
      unfold conditionalTailEnvelope
      repeat' rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(2 * (n : ℝ)) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) :=
      Real.exp_le_exp.mpr hexponent

/-- Summed exact radial-word cost for a buffered profile whose low side is
past the Taylor cutoff. -/
theorem tsum_buffered_exactProfileCost_le
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) (htail : profileUpperTailStart ≤ low) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (by omega) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal (Real.exp 9) *
        (ENNReal.ofReal (constrainedProfileWeight low profileUpperDelta) *
          (ENNReal.ofReal (Real.exp 360) *
            ENNReal.ofReal (conditionalTailEnvelope n (low + 4)))) := by
  calc
    _ ≤ ∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
        ENNReal.ofReal (Real.exp 9) *
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low (low + 4) m.1 *
              profileWeight m.1) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        exactProfileCost_le_exp_nine_mul_tilted hn hlow hstop m.2
    _ = ENNReal.ofReal (Real.exp 9) *
        (∑' m : {m : Profile n //
          IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low (low + 4) m.1 *
              profileWeight m.1)) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ _ := mul_le_mul' (le_refl _)
      (tsum_buffered_tiltedProfileWeight_le hn hlow hstop htail)

/-- The complete buffered exact-profile cost has the same public one-point
envelope as an ordinary constrained profile. -/
theorem tsum_buffered_exactProfileCost_le_exp
    {n low : ℕ} (hn : 5 ≤ n) (hlow : 2 ≤ low)
    (hstop : low + 4 ≤ n) (htail : profileUpperTailStart ≤ low) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low (low + 4) profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (by omega) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  have hraw := tsum_buffered_exactProfileCost_le hn hlow hstop htail
  have hprefix := constrainedProfileWeight_le_exp_core htail
  have hnOne : 1 ≤ n := by omega
  have hsubset : Finset.Ico (low + 4) n ⊆
      Finset.Ico profileUpperTailStart n := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    exact ⟨htail.trans (by omega), hj.2⟩
  have hharm : (∑ j ∈ Finset.Ico (low + 4) n, 1 / (j : ℝ)) ≤
      3 * (n : ℝ) ^ (3 / 5 : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j _ _ ↦ by positivity)).trans
        (harmonicTail_le_three_rpow hnOne)
  have hcore0 : 0 ≤ profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have ha : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
        profileUpperDelta 2 1 11 :=
      ProfileA11Assembly.a11ErrorCoefficient_nonneg
        (by norm_num [profileUpperDelta])
        (by norm_num) (by norm_num) (by norm_num)
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    have hstart0 : (0 : ℝ) ≤ profileUpperTailStart := Nat.cast_nonneg _
    nlinarith
  have ha11 : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
      profileUpperDelta 2 1 11 :=
    ProfileA11Assembly.a11ErrorCoefficient_nonneg
      (by norm_num [profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
  have hlowReal : (low : ℝ) ≤ n := by exact_mod_cast (show low ≤ n by omega)
  have hlowPow : (low : ℝ) ^ (3 / 5 : ℝ) ≤
      (n : ℝ) ^ (3 / 5 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hlowReal (by norm_num)
  have hcoreDom :
      ProfileA11Assembly.a11ErrorCoefficient profileUpperDelta 2 1 11 ≤
        profileUpperCoreConstant := by
    unfold profileUpperCoreConstant
    have hlog : 0 ≤ Real.log
        ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
        (constrainedProfiles profileUpperTailStart
          profileUpperDelta).card + 1 ≠ 0)
    have hstart0 : (0 : ℝ) ≤ profileUpperTailStart := Nat.cast_nonneg _
    nlinarith
  have hexponent :
      9 + (-(2 * (low : ℝ)) +
          profileUpperCoreConstant * (low : ℝ) ^ (3 / 5 : ℝ)) +
        (360 + (-(2 * (n - (low + 4) : ℕ) : ℝ) +
          ProfileA11Assembly.a11ErrorCoefficient
            profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
          ∑ j ∈ Finset.Ico (low + 4) n, 1 / (j : ℝ))) ≤
        -(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) := by
    have hcast : ((n - (low + 4) : ℕ) : ℝ) =
        (n : ℝ) - (low + 4 : ℕ) := by
      rw [Nat.cast_sub hstop]
    have hnPowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hnOne) (by norm_num)
    have hdelta : 3 * profileUpperDelta = (3 / 5 : ℝ) := by
      norm_num [profileUpperDelta]
    rw [hcast, hdelta]
    unfold profileUpperConstant
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at *
    nlinarith [hharm, hnPowOne,
      mul_le_mul_of_nonneg_left hlowPow hcore0,
      mul_le_mul_of_nonneg_right hcoreDom (by positivity :
        0 ≤ (n : ℝ) ^ (3 / 5 : ℝ))]
  apply hraw.trans
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 360)]
  rw [← ENNReal.ofReal_mul (constrainedProfileWeight_nonneg
    low profileUpperDelta)]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 9)]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp 9 *
        (constrainedProfileWeight low profileUpperDelta *
          (Real.exp 360 * conditionalTailEnvelope n (low + 4))) ≤
      Real.exp 9 *
        (Real.exp (-(2 * (low : ℝ)) +
            profileUpperCoreConstant * (low : ℝ) ^ (3 / 5 : ℝ)) *
          (Real.exp 360 * conditionalTailEnvelope n (low + 4))) := by
        gcongr
        exact mul_nonneg (Real.exp_nonneg _)
          (conditionalTailEnvelope_nonneg n (low + 4))
    _ = Real.exp
        (9 + (-(2 * (low : ℝ)) +
            profileUpperCoreConstant * (low : ℝ) ^ (3 / 5 : ℝ)) +
          (360 + (-(2 * (n - (low + 4) : ℕ) : ℝ) +
            ProfileA11Assembly.a11ErrorCoefficient
              profileUpperDelta 2 1 11 *
                (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
            ∑ j ∈ Finset.Ico (low + 4) n, 1 / (j : ℝ)))) := by
      unfold conditionalTailEnvelope
      repeat' rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(2 * (n : ℝ)) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) :=
      Real.exp_le_exp.mpr hexponent

lemma endpointTailWeight_nonneg
    (n start : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (a : ℕ) (delta : ℝ) :
    0 ≤ endpointTailWeight n start hstart hstartn a delta := by
  unfold endpointTailWeight
  exact Finset.sum_nonneg fun future _ ↦
    transitionSegmentProduct_nonneg start (n - start) _

/-- The endpoint tail can be read as an `ENNReal` `tsum` with finite
support. -/
theorem tsum_indicator_tail_eq_endpointTailWeight
    {n start a : ℕ} (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (delta : ℝ) :
    (∑' future : Fin (n - start) → ℕ,
      if future ∈ Fintype.piFinset
          (fun i : Fin (n - start) ↦
            allowedValues delta (start + 1 + i.1)) then
        ENNReal.ofReal
          (transitionSegmentProduct start (n - start)
            (profileAtScale
              (extendProfile hstart hstartn
                (endpointCenterProfile start a) future)))
      else 0) =
        ENNReal.ofReal
          (endpointTailWeight n start hstart hstartn a delta) := by
  let F := Fintype.piFinset
    (fun i : Fin (n - start) ↦
      allowedValues delta (start + 1 + i.1))
  rw [tsum_eq_sum (s := F)]
  · have hsum :
        (∑ future ∈ F,
          if future ∈ Fintype.piFinset
              (fun i : Fin (n - start) ↦
                allowedValues delta (start + 1 + i.1)) then
            ENNReal.ofReal
              (transitionSegmentProduct start (n - start)
                (profileAtScale
                  (extendProfile hstart hstartn
                    (endpointCenterProfile start a) future)))
          else 0) =
        ∑ future ∈ F,
          ENNReal.ofReal
            (transitionSegmentProduct start (n - start)
              (profileAtScale
                (extendProfile hstart hstartn
                  (endpointCenterProfile start a) future))) := by
        apply Finset.sum_congr rfl
        intro future hfuture
        rw [if_pos hfuture]
    rw [hsum]
    unfold endpointTailWeight
    rw [← ENNReal.ofReal_sum_of_nonneg]
    intro future _
    exact transitionSegmentProduct_nonneg start (n - start) _
  · intro future hfuture
    rw [if_neg hfuture]

/-! ## Buffers at the first four separation scales -/

/-- Every erased coordinate before a retained endpoint occurs in the head
profile through that endpoint. -/
theorem erasedProfileSum_le_head_sum
    {n low high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    (m : Profile n) :
    erasedProfileSum low high m ≤
      ∑ i : Fin (high - 1), profilePrefix hhigh hhighn m i := by
  let S := Finset.univ.filter
    (fun i : Fin (n - 1) ↦ ¬ RetainedCoordinate low high (scaleIndex i))
  let T := Finset.univ.filter
    (fun i : Fin (high - 1) ↦
      ¬ RetainedCoordinate low high (scaleIndex i))
  have heq :
      (∑ i ∈ S, m i) =
        ∑ i ∈ T, profilePrefix hhigh hhighn m i := by
    apply Finset.sum_bij (fun i hi ↦
      (⟨i.1, by
        have herased := (Finset.mem_filter.mp hi).2
        unfold RetainedCoordinate scaleIndex at herased
        omega⟩ : Fin (high - 1)))
    · intro i hi
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have herased := (Finset.mem_filter.mp hi).2
      simpa only [scaleIndex] using herased
    · intro i hi j hj hij
      have hv : i.1 = j.1 := congrArg
        (fun z : Fin (high - 1) ↦ z.1) hij
      exact Fin.ext hv
    · intro j hj
      let i : Fin (n - 1) := ⟨j.1, by have := j.2; omega⟩
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have herased := (Finset.mem_filter.mp hj).2
        simpa only [scaleIndex, i] using herased
      · apply Fin.ext
        rfl
    · intro i hi
      rfl
  unfold erasedProfileSum
  change (∑ i ∈ S, m i) ≤ _
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ ↦ Nat.zero_le _)

/-- A continuation joined to an arbitrary prefix is its literal Markov
path product from the prefix endpoint. -/
theorem transitionSegmentProduct_extendProfile_eq_path
    {n high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    (pref : Profile high) (future : Fin (n - high) → ℕ) :
    transitionSegmentProduct high (n - high)
        (profileAtScale (extendProfile hhigh hhighn pref future)) =
      pathTransitionProduct (n - high) (profileAtScale pref high) future := by
  let m := extendProfile hhigh hhighn pref future
  have hbase : profileAtScale m high = profileAtScale pref high := by
    have h := profileAtScale_profilePrefix hhigh hhighn m
    rw [profilePrefix_extendProfile] at h
    exact h.symm
  have hfuture : ∀ i : Fin (n - high),
      profileAtScale m (high + 1 + i.1) = future i := by
    intro i
    have h := profileFuture_eq_profileAtScale hhigh hhighn m i
    rw [profileFuture_extendProfile] at h
    exact h.symm
  change transitionSegmentProduct high (n - high) (profileAtScale m) = _
  rw [← pathTransitionProduct_profile (steps := n - high)
    (start := high) m]
  rw [hbase]
  congr 1
  funext i
  exact hfuture i

/-- Constrained tail factor after a short head profile. -/
def headTailFactor
    {n high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    (delta : ℝ) (head : Profile high)
    (tail : Fin (n - high) → ℕ) : ENNReal :=
  if profileAtScale head high ∈ allowedValues delta high then
      if tail ∈ Fintype.piFinset
          (fun i : Fin (n - high) ↦
            allowedValues delta (high + 1 + i.1)) then
        ENNReal.ofReal
          (endpointTailTerm n high hhigh hhighn
            (profileAtScale head high) tail)
      else 0
    else 0

/-- Split majorant for a buffer whose low endpoint is below scale two. -/
def shortHeadProfileMajorant
    {n high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    (r delta : ℝ)
    (p : Profile high × (Fin (n - high) → ℕ)) : ENNReal :=
  tiltedPathWeightENNReal (high - 1) r 1 p.1 *
    headTailFactor hhigh hhighn delta p.1 p.2

/-- One exact buffered profile with a short head is bounded by the split
tilted majorant. -/
theorem buffered_initial_summand_le_shortHeadProfileMajorant
    {n low high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    {r : ℝ} (hr : 1 ≤ r) {delta : ℝ} {m : Profile n}
    (hm : IsBufferedInternalProfile low high delta m) :
    ENNReal.ofReal
        (r ^ erasedProfileSum low high m *
          (firstProfileTransitionMass (hhigh.trans hhighn) m *
            profileWeight m)) ≤
      shortHeadProfileMajorant hhigh hhighn r delta
        (profileSplitEquiv hhigh hhighn m) := by
  let head := profilePrefix hhigh hhighn m
  let tail := profileFuture hhigh hhighn m
  have hend : profileAtScale head high ∈ allowedValues delta high := by
    dsimp only [head]
    rw [profileAtScale_profilePrefix hhigh hhighn]
    exact buffered_high_mem_allowedValues hhigh hhighn hm
  have htail : tail ∈ Fintype.piFinset
      (fun i : Fin (n - high) ↦
        allowedValues delta (high + 1 + i.1)) := by
    exact buffered_profileFuture_mem hhigh hhighn hm
  have hfirst : firstProfileTransitionMass (hhigh.trans hhighn) m =
      firstProfileTransitionMass hhigh head := by
    unfold firstProfileTransitionMass
    rfl
  have hweight :=
    ProfileConditionalTailUpper.profileWeight_eq_prefix_mul_tail
      hhigh hhighn m
  have htailEq :
      endpointTailTerm n high hhigh hhighn
          (profileAtScale head high) tail =
        transitionSegmentProduct high (n - high) (profileAtScale m) := by
    rw [endpointTailTerm_eq_pathTransitionProduct]
    rw [← transitionSegmentProduct_extendProfile_eq_path
      hhigh hhighn head tail]
    rw [extendProfile_profilePrefix_profileFuture]
  have hsum : erasedProfileSum low high m ≤ ∑ i, head i := by
    exact erasedProfileSum_le_head_sum hhigh hhighn m
  have hpow : r ^ erasedProfileSum low high m ≤ r ^ (∑ i, head i) :=
    pow_le_pow_right₀ hr hsum
  have hhead0 : 0 ≤ pathTransitionProduct (high - 1) 1 head :=
    pathTransitionProduct_nonneg _ _ _
  have htail0 : 0 ≤ transitionSegmentProduct high (n - high)
      (profileAtScale m) := transitionSegmentProduct_nonneg _ _ _
  have hlocal :
      ENNReal.ofReal
          (r ^ erasedProfileSum low high m *
            pathTransitionProduct (high - 1) 1 head) ≤
        tiltedPathWeightENNReal (high - 1) r 1 head := by
    rw [tiltedPathWeightENNReal_eq_ofReal _ r (by linarith)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hpow hhead0)
  rw [hweight, hfirst]
  change ENNReal.ofReal
      (r ^ erasedProfileSum low high m *
        (firstProfileTransitionMass hhigh head *
          (profileWeight head *
            transitionSegmentProduct high (n - high)
              (profileAtScale m)))) ≤ _
  rw [← mul_assoc (firstProfileTransitionMass hhigh head)
    (profileWeight head),
    firstProfileTransitionMass_mul_profileWeight_eq_path hhigh]
  change ENNReal.ofReal
      (r ^ erasedProfileSum low high m *
        (pathTransitionProduct (high - 1) 1 head *
          transitionSegmentProduct high (n - high) (profileAtScale m))) ≤ _
  rw [show r ^ erasedProfileSum low high m *
        (pathTransitionProduct (high - 1) 1 head *
          transitionSegmentProduct high (n - high) (profileAtScale m)) =
      (r ^ erasedProfileSum low high m *
        pathTransitionProduct (high - 1) 1 head) *
          transitionSegmentProduct high (n - high) (profileAtScale m) by ring]
  rw [ENNReal.ofReal_mul
    (mul_nonneg (pow_nonneg (by linarith) _) hhead0)]
  change _ ≤ tiltedPathWeightENNReal (high - 1) r 1 head *
    headTailFactor hhigh hhighn delta head tail
  unfold headTailFactor
  rw [if_pos hend, if_pos htail]
  exact mul_le_mul' hlocal (by
    rw [htailEq])

/-- All admissible continuations after a short retained endpoint are
bounded by the cutoff A.11 envelope. -/
theorem tsum_headTailFactor_le_cutoff
    {n high : ℕ} (hhigh : 2 ≤ high) (hhighn : high ≤ n)
    (hhighCutoff : high ≤ profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) (head : Profile high) :
    (∑' tail : Fin (n - high) → ℕ,
      headTailFactor hhigh hhighn profileUpperDelta head tail) ≤
        ENNReal.ofReal
          (conditionalTailEnvelope n profileUpperTailStart) := by
  by_cases hend : profileAtScale head high ∈
      allowedValues profileUpperDelta high
  · have hfun :
        (fun tail : Fin (n - high) → ℕ ↦
          headTailFactor hhigh hhighn profileUpperDelta head tail) =
        fun tail ↦
          if tail ∈ Fintype.piFinset
              (fun i : Fin (n - high) ↦
                allowedValues profileUpperDelta (high + 1 + i.1)) then
            ENNReal.ofReal
              (endpointTailTerm n high hhigh hhighn
                (profileAtScale head high) tail)
          else 0 := by
      funext tail
      simp only [headTailFactor, if_pos hend]
    rw [hfun, tsum_indicator_tail_eq_endpointTailWeight_early]
    exact ENNReal.ofReal_le_ofReal
      (endpointTailWeight_le_envelope_from_cutoff hhigh hhighCutoff
        hcutoffn hend)
  · have hfun :
        (fun tail : Fin (n - high) → ℕ ↦
          headTailFactor hhigh hhighn profileUpperDelta head tail) =
          fun _ ↦ 0 := by
      funext tail
      simp only [headTailFactor, if_neg hend]
    rw [hfun]
    simp

/-- The total tilted short-head majorant has one fixed bridge cost. -/
theorem tsum_shortHeadProfileMajorant_le
    {n high : ℕ} (hn : 5 ≤ n) (hhigh : 2 ≤ high)
    (hhighFive : high ≤ 5) (hhighn : high ≤ n)
    (hhighCutoff : high ≤ profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' p : Profile high × (Fin (n - high) → ℕ),
      shortHeadProfileMajorant hhigh hhighn
        ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p) ≤
      ENNReal.ofReal (Real.exp 360) *
        ENNReal.ofReal
          (conditionalTailEnvelope n profileUpperTailStart) := by
  change (∑' p : Profile high × (Fin (n - high) → ℕ),
    (fun head tail ↦ shortHeadProfileMajorant hhigh hhighn
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (head, tail))
      p.1 p.2) ≤ _
  have hprod := @ENNReal.tsum_prod
    (Profile high) (Fin (n - high) → ℕ)
    (fun head tail ↦ shortHeadProfileMajorant hhigh hhighn
      ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (head, tail))
  rw [hprod]
  calc
    (∑' head : Profile high,
        ∑' tail : Fin (n - high) → ℕ,
          shortHeadProfileMajorant hhigh hhighn
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta
              (head, tail)) =
      ∑' head : Profile high,
        tiltedPathWeightENNReal (high - 1)
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2) 1 head *
          (∑' tail : Fin (n - high) → ℕ,
            headTailFactor hhigh hhighn profileUpperDelta head tail) := by
      apply tsum_congr
      intro head
      unfold shortHeadProfileMajorant
      simp only [Prod.fst, Prod.snd]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' head : Profile high,
        tiltedPathWeightENNReal (high - 1)
            ((1 + 1 / (n : ℝ) ^ 4) ^ 2) 1 head *
          ENNReal.ofReal
            (conditionalTailEnvelope n profileUpperTailStart) := by
      apply ENNReal.tsum_le_tsum
      intro head
      exact mul_le_mul' (le_refl _)
        (tsum_headTailFactor_le_cutoff hhigh hhighn hhighCutoff
          hcutoffn head)
    _ = (∑' head : Profile high,
        tiltedPathWeightENNReal (high - 1)
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) 1 head) *
          ENNReal.ofReal
            (conditionalTailEnvelope n profileUpperTailStart) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal
            (conditionalTailEnvelope n profileUpperTailStart) := by
      apply mul_le_mul' _ (le_refl _)
      exact tsum_tiltedPathWeightENNReal_exactCutoff_le_exp_threeSixty
        (steps := high - 1) hn (by omega) (by
          have hsquare : 25 ≤ n ^ 2 := by
            simpa [pow_two] using Nat.mul_le_mul hn hn
          exact_mod_cast (show (1 : ℕ) ≤ 3 * n ^ 2 by omega))

/-- Reindex the short-buffer subtype into its head and tail coordinates. -/
theorem tsum_buffered_initial_tiltedWeight_le
    {n low high : ℕ} (hn : 5 ≤ n) (hhigh : 2 ≤ high)
    (hhighFive : high ≤ 5) (hhighn : high ≤ n)
    (hhighCutoff : high ≤ profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low high profileUpperDelta m},
      ENNReal.ofReal
        (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
            erasedProfileSum low high m.1 *
          (firstProfileTransitionMass (hhigh.trans hhighn) m.1 *
            profileWeight m.1))) ≤
      ENNReal.ofReal (Real.exp 360) *
        ENNReal.ofReal
          (conditionalTailEnvelope n profileUpperTailStart) := by
  let e := profileSplitEquiv hhigh hhighn
  let split : {m : Profile n //
      IsBufferedInternalProfile low high profileUpperDelta m} →
      Profile high × (Fin (n - high) → ℕ) := fun m ↦ e m.1
  have hsplit : Function.Injective split := by
    intro left right hlr
    apply Subtype.ext
    exact e.injective hlr
  have hr : (1 : ℝ) ≤ (1 + 1 / (n : ℝ) ^ 4) ^ 2 := by
    have heps : 0 ≤ 1 / (n : ℝ) ^ 4 := by positivity
    nlinarith [sq_nonneg (1 / (n : ℝ) ^ 4)]
  calc
    _ ≤ ∑' m : {m : Profile n //
          IsBufferedInternalProfile low high profileUpperDelta m},
        shortHeadProfileMajorant hhigh hhighn
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta (split m) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        buffered_initial_summand_le_shortHeadProfileMajorant
          hhigh hhighn hr m.2
    _ ≤ ∑' p : Profile high × (Fin (n - high) → ℕ),
        shortHeadProfileMajorant hhigh hhighn
          ((1 + 1 / (n : ℝ) ^ 4) ^ 2) profileUpperDelta p :=
      ENNReal.tsum_comp_le_tsum_of_injective hsplit _
    _ ≤ _ := tsum_shortHeadProfileMajorant_le hn hhigh hhighFive hhighn
      hhighCutoff hcutoffn

/-- The exact radial-word cost retains the normalized first transition in
the short-head case. -/
theorem exactProfileCost_le_exp_nine_mul_initial_tilted
    {n low high : ℕ} (hn : 5 ≤ n) (hhigh : 2 ≤ high)
    (hhighn : high ≤ n) {m : Profile n}
    (hm : IsBufferedInternalProfile low high profileUpperDelta m) :
    ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m *
          (firstProfileTransitionMass (hhigh.trans hhighn) m *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (hhigh.trans hhighn) m) *
            profileWeight m)) ≤
      ENNReal.ofReal (Real.exp 9) *
        ENNReal.ofReal
          (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
              erasedProfileSum low high m *
            (firstProfileTransitionMass (hhigh.trans hhighn) m *
              profileWeight m)) := by
  let r : ℝ := (1 + 1 / (n : ℝ) ^ 4) ^ 2
  let retained : ℝ :=
    (1 + 1 / (n : ℝ) ^ 4) ^
      (2 * (retainedProfileSum low high m + n ^ 3) + 1)
  let erased : ℝ := r ^ erasedProfileSum low high m
  let first : ℝ := firstProfileTransitionMass (hhigh.trans hhighn) m
  let terminal : ℝ :=
    TerminalNegativeBinomialWindow.terminalWindowMass n profileUpperDelta
      (TerminalNegativeBinomialWindow.terminalProfileCount
        (hhigh.trans hhighn) m)
  have hretained : retained ≤ Real.exp 9 :=
    retained_exactCutoffFactor_le_exp_nine hn
      (by norm_num [profileUpperDelta]) hm
  have hterminal : terminal ≤ 1 :=
    terminalWindowMass_le_one_of_buffered (by omega) hhighn
      (by norm_num [profileUpperDelta]) hm
  have hfirst0 : 0 ≤ first := by
    dsimp [first, firstProfileTransitionMass]
    exact transitionMass_nonneg _ _
  have hterminal0 : 0 ≤ terminal := by
    dsimp [terminal]
    exact TerminalNegativeBinomialWindow.terminalWindowMass_nonneg
      n profileUpperDelta _
        (ExcursionTransition.terminalSuccess_pos (by omega)).le
        (ExcursionTransition.terminalSuccess_le_one (by omega))
  have hweight0 := profileWeight_nonneg m
  have herased0 : 0 ≤ erased := by dsimp [erased, r]; positivity
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg 9)]
  apply ENNReal.ofReal_le_ofReal
  rw [exactCutoffFactor_eq_retained_mul_erased
    (low := low) (high := high) m]
  change retained * erased * (first * terminal * profileWeight m) ≤
    Real.exp 9 * (erased * (first * profileWeight m))
  calc
    retained * erased * (first * terminal * profileWeight m) ≤
        Real.exp 9 * erased * (first * 1 * profileWeight m) := by
      gcongr
    _ = Real.exp 9 * (erased * (first * profileWeight m)) := by ring

/-- The fixed short-head cost and the cutoff tail fit inside the public
one-point exponent. -/
theorem exp_nine_mul_bridge_mul_cutoffEnvelope_le_public
    {n : ℕ} (hcutoffn : profileUpperTailStart ≤ n) :
    Real.exp 9 *
        (Real.exp 360 *
          conditionalTailEnvelope n profileUpperTailStart) ≤
      Real.exp (-(2 * (n : ℝ)) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hnOne : 1 ≤ n :=
    (show 1 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans hcutoffn
  have hnPowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hnOne) (by norm_num)
  have hharm :
      (∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
        3 * (n : ℝ) ^ (3 / 5 : ℝ) :=
    harmonicTail_le_three_rpow hnOne
  have ha11 : 0 ≤ ProfileA11Assembly.a11ErrorCoefficient
      profileUpperDelta 2 1 11 :=
    ProfileA11Assembly.a11ErrorCoefficient_nonneg
      (by norm_num [profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.log
      ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      (constrainedProfiles profileUpperTailStart
        profileUpperDelta).card + 1 ≠ 0)
  have hcoef :
      ProfileA11Assembly.a11ErrorCoefficient
          profileUpperDelta 2 1 11 +
        2 * (profileUpperTailStart : ℝ) + 376 ≤
          profileUpperConstant := by
    unfold profileUpperConstant profileUpperCoreConstant
    nlinarith
  have hcast : ((n - profileUpperTailStart : ℕ) : ℝ) =
      (n : ℝ) - profileUpperTailStart := by
    rw [Nat.cast_sub hcutoffn]
  have hdelta : 3 * profileUpperDelta = (3 / 5 : ℝ) := by
    norm_num [profileUpperDelta]
  have hexponent :
      9 + 360 +
          (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            ProfileA11Assembly.a11ErrorCoefficient
                profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
            ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ)) ≤
        -(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) := by
    rw [hcast, hdelta]
    norm_num only [Nat.cast_ofNat] at *
    nlinarith [mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ (n : ℝ) ^ (3 / 5 : ℝ))]
  calc
    Real.exp 9 *
        (Real.exp 360 *
          conditionalTailEnvelope n profileUpperTailStart) =
      Real.exp
        (9 + 360 +
          (-(2 * (n - profileUpperTailStart : ℕ) : ℝ) +
            ProfileA11Assembly.a11ErrorCoefficient
                profileUpperDelta 2 1 11 *
              (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
            ∑ j ∈ Finset.Ico profileUpperTailStart n, 1 / (j : ℝ))) := by
      unfold conditionalTailEnvelope
      repeat' rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

/-- Complete exact-profile cost for all buffers whose retained endpoint is
among the first five scales. -/
theorem tsum_buffered_exactProfileCost_le_exp_short
    {n low high : ℕ} (hn : 5 ≤ n) (hhigh : 2 ≤ high)
    (hhighFive : high ≤ 5) (hhighn : high ≤ n)
    (hhighCutoff : high ≤ profileUpperTailStart)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile low high profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (hhigh.trans hhighn) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (hhigh.trans hhighn) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  calc
    _ ≤ ∑' m : {m : Profile n //
          IsBufferedInternalProfile low high profileUpperDelta m},
        ENNReal.ofReal (Real.exp 9) *
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low high m.1 *
              (firstProfileTransitionMass (hhigh.trans hhighn) m.1 *
                profileWeight m.1)) := by
      exact ENNReal.tsum_le_tsum fun m ↦
        exactProfileCost_le_exp_nine_mul_initial_tilted
          hn hhigh hhighn m.2
    _ = ENNReal.ofReal (Real.exp 9) *
        (∑' m : {m : Profile n //
          IsBufferedInternalProfile low high profileUpperDelta m},
          ENNReal.ofReal
            (((1 + 1 / (n : ℝ) ^ 4) ^ 2) ^
                erasedProfileSum low high m.1 *
              (firstProfileTransitionMass (hhigh.trans hhighn) m.1 *
                profileWeight m.1))) := by
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (Real.exp 9) *
        (ENNReal.ofReal (Real.exp 360) *
          ENNReal.ofReal
            (conditionalTailEnvelope n profileUpperTailStart)) := by
      exact mul_le_mul' (le_refl _)
        (tsum_buffered_initial_tiltedWeight_le hn hhigh hhighFive hhighn
          hhighCutoff hcutoffn)
    _ = ENNReal.ofReal
        (Real.exp 9 *
          (Real.exp 360 *
            conditionalTailEnvelope n profileUpperTailStart)) := by
      rw [ENNReal.ofReal_mul (Real.exp_nonneg 9),
        ENNReal.ofReal_mul (Real.exp_nonneg 360)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (exp_nine_mul_bridge_mul_cutoffEnvelope_le_public hcutoffn)

/-- Uniform exact-profile estimate for the three-coordinate buffer attached
to an arbitrary positive separation level. -/
theorem tsum_buffered_exactProfileCost_le_exp_separation
    {n l : ℕ} (hn : 5 ≤ n) (hl : 1 ≤ l) (hln : l + 1 ≤ n)
    (hcutoffn : profileUpperTailStart ≤ n) :
    (∑' m : {m : Profile n //
        IsBufferedInternalProfile (l - 3) (l + 1)
          profileUpperDelta m},
      ENNReal.ofReal
        ((1 + 1 / (n : ℝ) ^ 4) ^
            exactProfileRadialWordMaxTransitions m.1 *
          (firstProfileTransitionMass (by omega) m.1 *
            TerminalNegativeBinomialWindow.terminalWindowMass
              n profileUpperDelta
                (TerminalNegativeBinomialWindow.terminalProfileCount
                  (by omega) m.1) *
            profileWeight m.1))) ≤
      ENNReal.ofReal
        (Real.exp (-(2 * (n : ℝ)) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ))) := by
  by_cases hshort : l ≤ 4
  · exact tsum_buffered_exactProfileCost_le_exp_short hn (by omega)
      (by omega) hln
      (by norm_num [profileUpperTailStart]; omega) hcutoffn
  · have hlow : 2 ≤ l - 3 := by omega
    have hfour : (l - 3) + 4 = l + 1 := by omega
    by_cases hbefore : l - 3 < profileUpperTailStart
    · rw [← hfour]
      exact tsum_buffered_exactProfileCost_le_exp_small
        hn hlow (by omega) hbefore hcutoffn
    · have htail : profileUpperTailStart ≤ l - 3 := by omega
      rw [← hfour]
      exact tsum_buffered_exactProfileCost_le_exp
        hn hlow (by omega) htail

end

end Erdos1165.BufferedProfileMarkovUpper
