/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.FourierReturn

/-!
# The exact off-diagonal transition probability

This file proves the exact endpoint law for planar simple symmetric random walk.  Under the
diagonal change of coordinates

`(X, Y) ↦ (X + Y, X - Y)`,

one planar increment becomes a pair of independent signs.  Consequently the number of planar
paths from the origin to `(x, y)` in `n` steps is the product of two one-dimensional binomial
counts.  The definitions below include the range and parity obstruction explicitly.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165

/-! ## The diagonal bit transform -/

-- `boolSign` and `directionBits` are shared with `FourierReturn`.

@[simp] lemma directionBits_zero : directionBits 0 = (true, true) := rfl
@[simp] lemma directionBits_one : directionBits 1 = (false, false) := rfl
@[simp] lemma directionBits_two : directionBits 2 = (true, false) := rfl
@[simp] lemma directionBits_three : directionBits 3 = (false, true) := rfl

/-- The first diagonal sign of a direction is the sum of its Cartesian coordinates. -/
lemma directionVector_fst_add_snd (d : Direction) :
    (directionVector d).1 + (directionVector d).2 = boolSign (directionBits d).1 := by
  fin_cases d <;> rfl

/-- The second diagonal sign of a direction is the difference of its Cartesian coordinates. -/
lemma directionVector_fst_sub_snd (d : Direction) :
    (directionVector d).1 - (directionVector d).2 = boolSign (directionBits d).2 := by
  fin_cases d <;> rfl

/-- Splitting a direction-valued family gives two Boolean-valued families. -/
def splitDirectionBits (I : Type*) : (I → Direction) ≃ (I → Bool) × (I → Bool) where
  toFun ω := (fun i ↦ (directionBits (ω i)).1, fun i ↦ (directionBits (ω i)).2)
  invFun ab i := directionBits.symm (ab.1 i, ab.2 i)
  left_inv ω := by
    ext i
    change (directionBits.symm (directionBits (ω i))).val = (ω i).val
    exact congr_arg Fin.val (directionBits.symm_apply_apply (ω i))
  right_inv ab := by
    rcases ab with ⟨a, b⟩
    apply Prod.ext <;> funext i
    · exact congr_arg Prod.fst (directionBits.apply_symm_apply (a i, b i))
    · exact congr_arg Prod.snd (directionBits.apply_symm_apply (a i, b i))

/-! ## One-dimensional signs and their exact count -/

/-- The number of positive signs in a Boolean-valued finite family. -/
def positiveBitCount {I : Type*} [Fintype I] (a : I → Bool) : ℕ :=
  (Finset.univ.filter fun i ↦ a i = true).card

/-- The endpoint of the corresponding one-dimensional sign walk. -/
def signedEndpoint {I : Type*} [Fintype I] (a : I → Bool) : ℤ :=
  2 * positiveBitCount a - Fintype.card I

/-- The explicit range-and-parity condition for reaching `z` in `n` sign steps. -/
def OneDimAdmissible (n : ℕ) (z : ℤ) : Prop :=
  z.natAbs ≤ n ∧ (n - z.natAbs) % 2 = 0

instance instDecidableOneDimAdmissible (n : ℕ) (z : ℤ) :
    Decidable (OneDimAdmissible n z) := by
  unfold OneDimAdmissible
  infer_instance

/-- The binomial index in the symmetric formula: the number of signs of the minority type. -/
def oneDimMinorityIndex (n : ℕ) (z : ℤ) : ℕ :=
  (n - z.natAbs) / 2

/-- The exact number of one-dimensional sign paths ending at `z`. -/
noncomputable def oneDimEndpointCount (n : ℕ) (z : ℤ) : ℕ :=
  by
    classical
    exact if OneDimAdmissible n z then n.choose (oneDimMinorityIndex n z) else 0

/-- The corresponding one-dimensional probability mass. -/
noncomputable def oneDimEndpointMass (n : ℕ) (z : ℤ) : ℝ≥0∞ :=
  oneDimEndpointCount n z / 2 ^ n

/-- A finite direction family has the indicated Cartesian endpoint. -/
def finiteDirectionEndpoint {I : Type*} [Fintype I] (ω : I → Direction) : Point :=
  (∑ i, (directionVector (ω i)).1, ∑ i, (directionVector (ω i)).2)

lemma finiteDirectionEndpoint_eq_sum {I : Type*} [Fintype I] (ω : I → Direction) :
    finiteDirectionEndpoint ω = ∑ i, directionVector (ω i) := by
  classical
  have h (s : Finset I) :
      (∑ i ∈ s, (directionVector (ω i)).1, ∑ i ∈ s, (directionVector (ω i)).2) =
        ∑ i ∈ s, directionVector (ω i) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        rw [← ih]
        rfl
  simpa [finiteDirectionEndpoint] using h Finset.univ

lemma sum_boolSign_eq_signedEndpoint {I : Type*} [Fintype I] (a : I → Bool) :
    (∑ i, boolSign (a i)) = signedEndpoint a := by
  classical
  rw [show (∑ i, boolSign (a i)) =
      ∑ i, ((2 : ℤ) * (if a i = true then 1 else 0) - 1) by
    apply Finset.sum_congr rfl
    intro i _
    cases a i <;> norm_num [boolSign]]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [signedEndpoint, positiveBitCount]

/-- The diagonal coordinates of a finite planar path are the endpoints of the two sign paths. -/
lemma finiteDirectionEndpoint_diagonal {I : Type*} [Fintype I] (ω : I → Direction) :
    let ab := splitDirectionBits I ω
    (finiteDirectionEndpoint ω).1 + (finiteDirectionEndpoint ω).2 = signedEndpoint ab.1 ∧
      (finiteDirectionEndpoint ω).1 - (finiteDirectionEndpoint ω).2 = signedEndpoint ab.2 := by
  dsimp only
  constructor
  · rw [← sum_boolSign_eq_signedEndpoint]
    simp only [finiteDirectionEndpoint, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa [splitDirectionBits] using directionVector_fst_add_snd (ω i)
  · rw [← sum_boolSign_eq_signedEndpoint]
    simp only [finiteDirectionEndpoint, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa [splitDirectionBits] using directionVector_fst_sub_snd (ω i)

/-- Equality of Cartesian endpoints is equivalent to equality of the two diagonal endpoints. -/
lemma finiteDirectionEndpoint_eq_iff {I : Type*} [Fintype I] (ω : I → Direction)
    (x : Point) :
    finiteDirectionEndpoint ω = x ↔
      signedEndpoint (splitDirectionBits I ω).1 = x.1 + x.2 ∧
        signedEndpoint (splitDirectionBits I ω).2 = x.1 - x.2 := by
  have hdiag := finiteDirectionEndpoint_diagonal ω
  constructor
  · intro h
    rw [h] at hdiag
    exact ⟨hdiag.1.symm, hdiag.2.symm⟩
  · rintro ⟨h₁, h₂⟩
    apply Prod.ext
    · omega
    · omega

/-! ### Arithmetic form of the range-and-parity condition -/

lemma oneDimAdmissible_iff_exists (n : ℕ) (z : ℤ) :
    OneDimAdmissible n z ↔
      ∃ k : ℕ, k ≤ n ∧ (2 : ℤ) * k - n = z := by
  constructor
  · rintro ⟨habs, hpar⟩
    obtain ⟨a, ha⟩ := (Nat.even_iff.mpr hpar)
    by_cases hz : 0 ≤ z
    · have hzabs : (z.natAbs : ℤ) = z := by simpa using Int.natAbs_of_nonneg hz
      refine ⟨n - a, by omega, ?_⟩
      omega
    · have hz' : z < 0 := lt_of_not_ge hz
      have hzabs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz'.le
      refine ⟨a, by omega, ?_⟩
      omega
  · rintro ⟨k, hk, hkz⟩
    by_cases hz : 0 ≤ z
    · have hzabs : (z.natAbs : ℤ) = z := by simpa using Int.natAbs_of_nonneg hz
      refine ⟨by omega, Nat.even_iff.mp ⟨n - k, by omega⟩⟩
    · have hz' : z < 0 := lt_of_not_ge hz
      have hzabs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hz'.le
      refine ⟨by omega, Nat.even_iff.mp ⟨k, by omega⟩⟩

lemma oneDimAdmissible_of_endpoint {n k : ℕ} {z : ℤ} (hk : k ≤ n)
    (hz : (2 : ℤ) * k - n = z) : OneDimAdmissible n z :=
  (oneDimAdmissible_iff_exists n z).2 ⟨k, hk, hz⟩

lemma endpoint_count_choose_minority {n k : ℕ} {z : ℤ} (hk : k ≤ n)
    (hz : (2 : ℤ) * k - n = z) :
    n.choose k = n.choose (oneDimMinorityIndex n z) := by
  have hadm := oneDimAdmissible_of_endpoint hk hz
  obtain ⟨a, ha⟩ := Nat.even_iff.mpr hadm.2
  have haa : (a + a) / 2 = a := by omega
  rw [oneDimMinorityIndex, ha, haa]
  by_cases hz0 : 0 ≤ z
  · have hzabs : (z.natAbs : ℤ) = z := by simpa using Int.natAbs_of_nonneg hz0
    have hka : k = n - a := by omega
    rw [hka, Nat.choose_symm]
    omega
  · have hzneg : z < 0 := lt_of_not_ge hz0
    have hzabs : (z.natAbs : ℤ) = -z := Int.ofNat_natAbs_of_nonpos hzneg.le
    congr
    omega

/-! ### Counting Boolean sign paths -/

/-- A Boolean-valued family is equivalently its finite set of `true` positions. -/
noncomputable def bitSupportEquiv (I : Type*) [Fintype I] : (I → Bool) ≃ Finset I := by
  classical
  exact
    { toFun := fun a ↦ Finset.univ.filter fun i ↦ a i = true
      invFun := fun s i ↦ decide (i ∈ s)
      left_inv := fun a ↦ by
        funext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        cases a i <;> simp
      right_inv := fun s ↦ by ext i; simp }

@[simp] lemma bitSupportEquiv_card {I : Type*} [Fintype I] (a : I → Bool) :
    (bitSupportEquiv I a).card = positiveBitCount a := rfl

/-- Boolean families with exactly `k` positive signs are counted by `choose`. -/
lemma card_bit_paths_with_count (I : Type*) [Fintype I] (k : ℕ) :
    Nat.card {a : I → Bool // positiveBitCount a = k} =
      (Fintype.card I).choose k := by
  classical
  let e : {a : I → Bool // positiveBitCount a = k} ≃ Set.powersetCard I k :=
    { toFun := fun a ↦ ⟨bitSupportEquiv I a, by simpa using a.2⟩
      invFun := fun s ↦ ⟨(bitSupportEquiv I).symm s.1, by
        rw [← bitSupportEquiv_card, (bitSupportEquiv I).apply_symm_apply]
        exact s.2⟩
      left_inv := fun a ↦ by apply Subtype.ext; exact (bitSupportEquiv I).symm_apply_apply a
      right_inv := fun s ↦ by apply Subtype.ext; exact (bitSupportEquiv I).apply_symm_apply s }
  rw [Nat.card_congr e, Set.powersetCard.card, Nat.card_eq_fintype_card]

lemma card_signedEndpoint_fiber (I : Type*) [Fintype I] (z : ℤ) :
    Nat.card {a : I → Bool // signedEndpoint a = z} =
      oneDimEndpointCount (Fintype.card I) z := by
  classical
  unfold oneDimEndpointCount
  split_ifs with hadm
  · obtain ⟨k, hk, hkz⟩ := (oneDimAdmissible_iff_exists (Fintype.card I) z).1 hadm
    let e : {a : I → Bool // signedEndpoint a = z} ≃
        {a : I → Bool // positiveBitCount a = k} :=
      Equiv.subtypeEquiv (Equiv.refl _) fun a ↦ by
        simp only [Equiv.refl_apply, signedEndpoint]
        constructor <;> intro h <;> omega
    rw [Nat.card_congr e, card_bit_paths_with_count]
    exact endpoint_count_choose_minority hk hkz
  · rw [Nat.card_eq_zero]
    left
    constructor
    intro a
    apply hadm
    have hk : positiveBitCount a.1 ≤ Fintype.card I := by
      unfold positiveBitCount
      simpa using Finset.card_le_card (Finset.filter_subset (s := Finset.univ)
        (p := fun i ↦ a.1 i = true))
    exact oneDimAdmissible_of_endpoint hk (by simpa [signedEndpoint] using a.2)

/-! ## The product count for planar paths -/

/-- The exact number of planar direction strings with a specified endpoint. -/
noncomputable def planarEndpointCount (n : ℕ) (x : Point) : ℕ :=
  oneDimEndpointCount n (x.1 + x.2) * oneDimEndpointCount n (x.1 - x.2)

/-- The range-and-parity condition for a planar endpoint, in diagonal coordinates. -/
def PlanarAdmissible (n : ℕ) (x : Point) : Prop :=
  OneDimAdmissible n (x.1 + x.2) ∧ OneDimAdmissible n (x.1 - x.2)

instance instDecidablePlanarAdmissible (n : ℕ) (x : Point) :
    Decidable (PlanarAdmissible n x) := by
  unfold PlanarAdmissible
  infer_instance

@[simp] lemma oneDimEndpointCount_of_admissible {n : ℕ} {z : ℤ}
    (h : OneDimAdmissible n z) :
    oneDimEndpointCount n z = n.choose (oneDimMinorityIndex n z) := by
  simp [oneDimEndpointCount, h]

@[simp] lemma oneDimEndpointCount_of_not_admissible {n : ℕ} {z : ℤ}
    (h : ¬OneDimAdmissible n z) : oneDimEndpointCount n z = 0 := by
  simp [oneDimEndpointCount, h]

/-- Expanded piecewise form of the planar count, displaying both range-and-parity tests. -/
theorem planarEndpointCount_eq_ite (n : ℕ) (x : Point) :
    planarEndpointCount n x =
      if PlanarAdmissible n x then
        n.choose (oneDimMinorityIndex n (x.1 + x.2)) *
          n.choose (oneDimMinorityIndex n (x.1 - x.2))
      else 0 := by
  classical
  by_cases h₁ : OneDimAdmissible n (x.1 + x.2) <;>
    by_cases h₂ : OneDimAdmissible n (x.1 - x.2) <;>
    simp [planarEndpointCount, PlanarAdmissible, h₁, h₂]

/-- The diagonal transform sends the planar endpoint fiber bijectively to a product of two
one-dimensional endpoint fibers. -/
noncomputable def finiteEndpointFiberEquiv (I : Type*) [Fintype I] (x : Point) :
    { ω : I → Direction // finiteDirectionEndpoint ω = x } ≃
      { a : I → Bool // signedEndpoint a = x.1 + x.2 } ×
        { b : I → Bool // signedEndpoint b = x.1 - x.2 } where
  toFun ω :=
    let ab := splitDirectionBits I ω.1
    ⟨⟨ab.1, ((finiteDirectionEndpoint_eq_iff ω.1 x).1 ω.2).1⟩,
      ⟨ab.2, ((finiteDirectionEndpoint_eq_iff ω.1 x).1 ω.2).2⟩⟩
  invFun ab :=
    ⟨(splitDirectionBits I).symm (ab.1.1, ab.2.1),
      (finiteDirectionEndpoint_eq_iff _ x).2 (by
        simpa using And.intro ab.1.2 ab.2.2)⟩
  left_inv ω := by
    apply Subtype.ext
    exact (splitDirectionBits I).symm_apply_apply ω.1
  right_inv ab := by
    rcases ab with ⟨a, b⟩
    apply Prod.ext <;> apply Subtype.ext
    · exact congr_arg Prod.fst ((splitDirectionBits I).apply_symm_apply (a.1, b.1))
    · exact congr_arg Prod.snd ((splitDirectionBits I).apply_symm_apply (a.1, b.1))

/-- Exact combinatorial product formula for the planar endpoint fiber. -/
theorem card_finiteDirectionEndpoint_fiber (I : Type*) [Fintype I] (x : Point) :
    Nat.card { ω : I → Direction // finiteDirectionEndpoint ω = x } =
      planarEndpointCount (Fintype.card I) x := by
  rw [Nat.card_congr (finiteEndpointFiberEquiv I x), Nat.card_prod,
    card_signedEndpoint_fiber, card_signedEndpoint_fiber]
  rfl

/-! ## From finite counting to the random-walk transition probability -/

/-- Restriction of an infinite increment sequence to its first `n` entries. -/
def finiteSteps (n : ℕ) (ω : StepPath) : Fin n → Direction :=
  fun i ↦ ω i

lemma measurable_finiteSteps (n : ℕ) : Measurable (finiteSteps n) := by
  unfold finiteSteps
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i : ℕ)

/-- The first `n` directions are uniformly distributed among all `4^n` direction strings. -/
lemma fairSteps_map_finiteSteps (n : ℕ) :
    fairSteps.map (finiteSteps n) =
      ProbabilityTheory.uniformOn (Set.univ : Set (Fin n → Direction)) := by
  rw [fairSteps]
  change (Measure.infinitePi fun _ : ℕ ↦ fairStep).map
    (fun ω (i : Fin n) ↦ ω (i : ℕ)) = _
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (f := fun i : Fin n ↦ (i : ℕ)) Fin.val_injective]
  rw [Measure.infinitePi_eq_pi]
  simpa [fairStep] using
    (ProbabilityTheory.uniformOn_pi
      (f := fun _ : Fin n ↦ (Set.univ : Set Direction))).symm

lemma fairSteps_finiteSteps_apply (n : ℕ) (A : Set (Fin n → Direction)) :
    fairSteps {ω | finiteSteps n ω ∈ A} =
      Measure.count A / (4 : ℝ≥0∞) ^ n := by
  change fairSteps ((finiteSteps n) ⁻¹' A) = _
  rw [← Measure.map_apply (measurable_finiteSteps n) (by measurability)]
  rw [fairSteps_map_finiteSteps, ProbabilityTheory.uniformOn_univ]
  simp

lemma finiteDirectionEndpoint_finiteSteps (ω : StepPath) (n : ℕ) :
    finiteDirectionEndpoint (finiteSteps n ω) = trajectory ω n := by
  rw [finiteDirectionEndpoint_eq_sum, trajectory]
  change (∑ i : Fin n, directionVector (ω (i : ℕ))) =
    ∑ i ∈ Finset.range n, directionVector (ω i)
  exact Fin.sum_univ_eq_sum_range (fun i ↦ directionVector (ω i)) n

/-- The finite set of direction strings ending at `x`. -/
def endpointFiber (n : ℕ) (x : Point) : Set (Fin n → Direction) :=
  {u | finiteDirectionEndpoint u = x}

/-- Endpoint probability expressed as the cardinality of the finite endpoint fiber. -/
lemma simpleRandomWalk_endpoint_apply_ncard (n : ℕ) (x : Point) :
    simpleRandomWalk {s | s n = x} =
      ((endpointFiber n x).ncard : ℝ≥0∞) / (4 : ℝ≥0∞) ^ n := by
  rw [simpleRandomWalk]
  have hset : MeasurableSet ({s : WalkPath | s n = x}) :=
    measurableSet_eq_fun (measurable_pi_apply n) measurable_const
  rw [Measure.map_apply measurable_trajectory hset]
  change fairSteps {ω | trajectory ω n = x} = _
  rw [show {ω | trajectory ω n = x} =
      {ω | finiteSteps n ω ∈ endpointFiber n x} by
    ext ω
    simp only [Set.mem_ofPred_eq, endpointFiber]
    rw [finiteDirectionEndpoint_finiteSteps]]
  rw [fairSteps_finiteSteps_apply]
  have hfinite : (endpointFiber n x).Finite := Set.toFinite _
  rw [Measure.count_apply_finite _ hfinite]
  rw [Set.ncard_eq_toFinset_card _ hfinite]

lemma endpointFiber_ncard (n : ℕ) (x : Point) :
    (endpointFiber n x).ncard = planarEndpointCount n x := by
  rw [← Nat.card_coe_set_eq]
  change Nat.card { ω : Fin n → Direction // finiteDirectionEndpoint ω = x } =
    planarEndpointCount n x
  simpa using card_finiteDirectionEndpoint_fiber (Fin n) x

/-- Exact endpoint formula for planar simple symmetric random walk. -/
theorem simpleRandomWalk_endpoint_apply (n : ℕ) (x : Point) :
    simpleRandomWalk {s | s n = x} =
      (planarEndpointCount n x : ℝ≥0∞) / (4 : ℝ≥0∞) ^ n := by
  rw [simpleRandomWalk_endpoint_apply_ncard, endpointFiber_ncard]

/-- Product form: after the diagonal transform the two endpoint masses are independent. -/
theorem simpleRandomWalk_endpoint_apply_product (n : ℕ) (x : Point) :
    simpleRandomWalk {s | s n = x} =
      oneDimEndpointMass n (x.1 + x.2) * oneDimEndpointMass n (x.1 - x.2) := by
  rw [simpleRandomWalk_endpoint_apply]
  simp only [oneDimEndpointMass, planarEndpointCount, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  rw [show (4 : ℝ≥0∞) ^ n = (2 : ℝ≥0∞) ^ n * (2 : ℝ≥0∞) ^ n by
    rw [← mul_pow]
    norm_num, ENNReal.mul_inv (by simp) (by simp)]
  ac_rfl

/-- Fully expanded range/parity case distinction for the planar transition probability. -/
theorem simpleRandomWalk_endpoint_apply_ite (n : ℕ) (x : Point) :
    simpleRandomWalk {s | s n = x} =
      if PlanarAdmissible n x then
        ((n.choose (oneDimMinorityIndex n (x.1 + x.2)) *
          n.choose (oneDimMinorityIndex n (x.1 - x.2)) : ℕ) : ℝ≥0∞) /
            (4 : ℝ≥0∞) ^ n
      else 0 := by
  rw [simpleRandomWalk_endpoint_apply, planarEndpointCount_eq_ite]
  split_ifs <;> simp

/-! ## Useful special cases -/

@[simp] lemma oneDimEndpointCount_even_zero (m : ℕ) :
    oneDimEndpointCount (2 * m) 0 = (2 * m).choose m := by
  simp [oneDimEndpointCount, OneDimAdmissible, oneDimMinorityIndex]

@[simp] lemma oneDimEndpointCount_odd_zero (m : ℕ) :
    oneDimEndpointCount (2 * m + 1) 0 = 0 := by
  simp [oneDimEndpointCount, OneDimAdmissible]

@[simp] lemma planarEndpointCount_even_origin (m : ℕ) :
    planarEndpointCount (2 * m) (0, 0) = ((2 * m).choose m) ^ 2 := by
  simp [planarEndpointCount, pow_two]

@[simp] lemma planarEndpointCount_odd_origin (m : ℕ) :
    planarEndpointCount (2 * m + 1) (0, 0) = 0 := by
  simp [planarEndpointCount]

/-- The classical exact return probability at even times. -/
theorem simpleRandomWalk_even_return (m : ℕ) :
    simpleRandomWalk {s | s (2 * m) = (0, 0)} =
      (((2 * m).choose m : ℕ) : ℝ≥0∞) ^ 2 / (4 : ℝ≥0∞) ^ (2 * m) := by
  rw [simpleRandomWalk_endpoint_apply]
  simp

/-- The walk cannot return to the origin at an odd time. -/
theorem simpleRandomWalk_odd_return (m : ℕ) :
    simpleRandomWalk {s | s (2 * m + 1) = (0, 0)} = 0 := by
  rw [simpleRandomWalk_endpoint_apply]
  simp

/-! ## The sharp on-diagonal local limit -/

/-- Wallis' product gives an exact normalization identity for the return mass. -/
lemma mul_planarReturnProbability_eq_wallis (n : ℕ) :
    (n : ℝ) * planarReturnProbability n =
      ((n : ℝ) / (2 * n + 1)) / Real.Wallis.W n := by
  have hfac :
      (Nat.choose (2 * n) n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) =
        ((2 * n).factorial : ℝ) := by
    exact_mod_cast (by
      simpa [two_mul] using Nat.choose_mul_factorial_mul_factorial
        (Nat.le_mul_of_pos_left n (by omega : 0 < 2)))
  rw [Real.Wallis.W_eq_factorial_ratio]
  unfold planarReturnProbability
  field_simp
  rw [← hfac]
  have hp : (2 : ℝ) ^ (4 * n) = 16 ^ n := by
    rw [pow_mul]
    norm_num
  rw [hp]
  simp only [Nat.centralBinom, two_mul]
  ring

/-- Sharp local limit at the origin: `n P(S_(2n)=0) → 1/π`. -/
theorem tendsto_mul_planarReturnProbability :
    Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * planarReturnProbability n) Filter.atTop
      (nhds (1 / Real.pi)) := by
  have hratio :
      Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) / (2 * n + 1)) Filter.atTop (nhds (1 / 2)) :=
    Stirling.tendsto_self_div_two_mul_self_add_one
  have hW : Filter.Tendsto (fun n : ℕ ↦ (Real.Wallis.W n)⁻¹) Filter.atTop
      (nhds ((Real.pi / 2)⁻¹)) :=
    Real.Wallis.tendsto_W_nhds_pi_div_two.inv₀ (by positivity)
  have h := hratio.mul hW
  convert h using 1
  · funext n
    rw [mul_planarReturnProbability_eq_wallis, div_eq_mul_inv]
  · field_simp

end Erdos1165
