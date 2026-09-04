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

import Mathlib

/-!
# The switching argument for Erdős Problem 88

This file formalizes the exact, finite part of Section 13 of
Kwan--Sah--Sauermann--Sawhney.  There is no probability-space bookkeeping:
expectations under the uniform measure are finite sums divided by a common
positive constant, so the reversal identity is proved first as an equality
of cardinalities.

The graph-specific set `switchingPairs` is the set called `T` in the paper.
For an integer-valued statistic `score`, `switchingCount` is the random
variable `Y_ℓ`.  The equivalence `reverseConfigurationEquiv` reverses one
switch and proves the exact identity

`E[Y_ℓ Z_x] = E[Y_{-ℓ} Z_{x+ℓ}]`.

The final part contains the two Cauchy--Schwarz steps used to pass from the
raw moment estimates of Lemma 13.4 to a lower bound at one exact point.
-/

open scoped BigOperators

namespace Erdos88
namespace Switching

universe u v

section GraphPairs

variable {V : Type u} [Fintype V]

/-- The number of vertices of `S₀` adjacent to `z` but not to `y`. -/
noncomputable def exclusiveNeighborCount (G : SimpleGraph V) (S₀ : Finset V)
    (z y : V) : ℕ :=
  by
    classical
    exact (S₀.filter fun w ↦ G.Adj z w ∧ ¬G.Adj y w).card

/-- The finite, threshold-valued version of the set `T` in KSSS (4.50).

In the application `q` is a natural-number rounding of `ρ² |S₀|`.
Both directed exclusive-neighborhood conditions are included, hence this
finset is invariant under reversing a pair. -/
noncomputable def switchingPairs (G : SimpleGraph V) (S S₀ : Finset V)
    (q : ℕ) : Finset (V × V) :=
  by
    classical
    exact (S ×ˢ S).filter fun yz ↦
      q ≤ exclusiveNeighborCount G S₀ yz.2 yz.1 ∧
        q ≤ exclusiveNeighborCount G S₀ yz.1 yz.2

lemma mem_switchingPairs_iff (G : SimpleGraph V) (S S₀ : Finset V)
    (q : ℕ) (y z : V) :
    (y, z) ∈ switchingPairs G S S₀ q ↔
      y ∈ S ∧ z ∈ S ∧
        q ≤ exclusiveNeighborCount G S₀ z y ∧
        q ≤ exclusiveNeighborCount G S₀ y z := by
  classical
  simp [switchingPairs, and_assoc]

/-- Reversing an admissible graph pair remains admissible. -/
lemma switchingPairs_symm (G : SimpleGraph V) (S S₀ : Finset V)
    (q : ℕ) (y z : V) :
    (y, z) ∈ switchingPairs G S S₀ q ↔
      (z, y) ∈ switchingPairs G S S₀ q := by
  rw [mem_switchingPairs_iff, mem_switchingPairs_iff]
  aesop

end GraphPairs

section ExactSwitch

variable {V : Type u} [Fintype V]

/-- Replace `y` by `z` in a finite vertex set. -/
noncomputable def swapSubset (U : Finset V) (y z : V) : Finset V := by
  classical
  exact insert z (U.erase y)

@[simp] lemma mem_swapSubset_right (U : Finset V) (y z : V) :
    z ∈ swapSubset U y z := by
  simp [swapSubset]

lemma not_mem_swapSubset_left {U : Finset V} {y z : V}
    (hy : y ∈ U) (hz : z ∉ U) : y ∉ swapSubset U y z := by
  classical
  intro h
  simp only [swapSubset, Finset.mem_insert, Finset.mem_erase] at h
  rcases h with h | h
  · exact hz (h ▸ hy)
  · exact h.1 rfl

/-- An admissible replacement is undone by reversing its ordered pair. -/
lemma swapSubset_reverse {U : Finset V} {y z : V}
    (hy : y ∈ U) (hz : z ∉ U) :
    swapSubset (swapSubset U y z) z y = U := by
  classical
  ext w
  by_cases hwy : w = y
  · subst w
    simp [swapSubset, hy, hz]
  · by_cases hwz : w = z
    · subst w
      simp [swapSubset, hy, hz]
    · simp [swapSubset, hwy, hwz]

/-- The signed change of an integer-valued statistic under one switch. -/
noncomputable def switchIncrement (score : Finset V → ℤ) (U : Finset V)
    (y z : V) : ℤ :=
  score (swapSubset U y z) - score U

/-- Reversing a valid switch negates its increment. -/
lemma switchIncrement_reverse (score : Finset V → ℤ)
    {U : Finset V} {y z : V} (hy : y ∈ U) (hz : z ∉ U) :
    switchIncrement score (swapSubset U y z) z y =
      -switchIncrement score U y z := by
  simp [switchIncrement, swapSubset_reverse hy hz]

/-- Symmetry of an abstract finset of ordered switch pairs. -/
def IsSymmetric (T : Finset (V × V)) : Prop :=
  ∀ y z, (y, z) ∈ T ↔ (z, y) ∈ T

lemma switchingPairs_isSymmetric (G : SimpleGraph V) (S S₀ : Finset V)
    (q : ℕ) : IsSymmetric (switchingPairs G S S₀ q) := by
  intro y z
  exact switchingPairs_symm G S S₀ q y z

/-- `Y_ℓ(U)`: the number of admissible switches out of `U` having
increment exactly `ℓ`. -/
noncomputable def switchingCount (T : Finset (V × V))
    (score : Finset V → ℤ) (ℓ : ℤ) (U : Finset V) : ℕ :=
  by
    classical
    exact (T.filter fun yz : V × V ↦
      yz.1 ∈ U ∧ yz.2 ∉ U ∧
        switchIncrement score U yz.1 yz.2 = ℓ).card

/-- A switch counted by `Y_ℓ` whose initial score is `x`. -/
def SwitchConfiguration (T : Finset (V × V))
    (score : Finset V → ℤ) (ℓ x : ℤ) :=
  {c : Finset V × (V × V) //
    c.2 ∈ T ∧ c.2.1 ∈ c.1 ∧ c.2.2 ∉ c.1 ∧
      score c.1 = x ∧
      switchIncrement score c.1 c.2.1 c.2.2 = ℓ}

noncomputable instance switchConfigurationFintype
    (T : Finset (V × V)) (score : Finset V → ℤ) (ℓ x : ℤ) :
    Fintype (SwitchConfiguration T score ℓ x) := by
  classical
  unfold SwitchConfiguration
  infer_instance

/-- Reverse a single switching configuration. -/
noncomputable def reverseConfiguration {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) {ℓ x : ℤ} :
    SwitchConfiguration T score ℓ x →
      SwitchConfiguration T score (-ℓ) (x + ℓ) := by
  classical
  rintro ⟨⟨U, ⟨y, z⟩⟩, hyz, hy, hz, hx, hinc⟩
  refine ⟨⟨swapSubset U y z, ⟨z, y⟩⟩, ?_⟩
  refine ⟨(hT y z).mp hyz, mem_swapSubset_right U y z,
    not_mem_swapSubset_left hy hz, ?_, ?_⟩
  · change score (swapSubset U y z) = x + ℓ
    change score U = x at hx
    change score (swapSubset U y z) - score U = ℓ at hinc
    omega
  · simpa only [switchIncrement_reverse score hy hz, hinc]

@[simp] lemma reverseConfiguration_val {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) {ℓ x : ℤ}
    (c : SwitchConfiguration T score ℓ x) :
    (reverseConfiguration hT c).val =
      (swapSubset c.val.1 c.val.2.1 c.val.2.2,
        (c.val.2.2, c.val.2.1)) := by
  rcases c with ⟨⟨U, ⟨y, z⟩⟩, hyz, hy, hz, hx, hinc⟩
  rfl

/-- Reverse a target configuration back to its source, with the arithmetic
indices presented in their original (rather than normalized) form. -/
noncomputable def reverseConfigurationBack {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) {ℓ x : ℤ} :
    SwitchConfiguration T score (-ℓ) (x + ℓ) →
      SwitchConfiguration T score ℓ x := by
  classical
  rintro ⟨⟨U, ⟨z, y⟩⟩, hzy, hz, hy, hx, hinc⟩
  refine ⟨⟨swapSubset U z y, ⟨y, z⟩⟩, ?_⟩
  refine ⟨(hT y z).mpr hzy, mem_swapSubset_right U z y,
    not_mem_swapSubset_left hz hy, ?_, ?_⟩
  · change score (swapSubset U z y) = x
    change score U = x + ℓ at hx
    change score (swapSubset U z y) - score U = -ℓ at hinc
    omega
  · simpa only [switchIncrement_reverse score hz hy, hinc, neg_neg]

@[simp] lemma reverseConfigurationBack_val {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) {ℓ x : ℤ}
    (c : SwitchConfiguration T score (-ℓ) (x + ℓ)) :
    (reverseConfigurationBack hT c).val =
      (swapSubset c.val.1 c.val.2.1 c.val.2.2,
        (c.val.2.2, c.val.2.1)) := by
  rcases c with ⟨⟨U, ⟨z, y⟩⟩, hzy, hz, hy, hx, hinc⟩
  rfl

/-- Reversing switches is an equivalence between the configurations counted
by the two sides of the KSSS reversal identity. -/
noncomputable def reverseConfigurationEquiv {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) (ℓ x : ℤ) :
    SwitchConfiguration T score ℓ x ≃
      SwitchConfiguration T score (-ℓ) (x + ℓ) where
  toFun := reverseConfiguration hT
  invFun := reverseConfigurationBack hT
  left_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨U, ⟨y, z⟩⟩, hyz, hy, hz, hx, hinc⟩
    simp only [reverseConfigurationBack_val, reverseConfiguration_val]
    exact Prod.ext (swapSubset_reverse hy hz) rfl
  right_inv c := by
    apply Subtype.ext
    rcases c with ⟨⟨U, ⟨z, y⟩⟩, hyz, hz, hy, hx, hinc⟩
    simp only [reverseConfiguration_val, reverseConfigurationBack_val]
    exact Prod.ext (swapSubset_reverse hz hy) rfl

/-- The unnormalised expectation `∑_U Y_ℓ(U) Z_x(U)`, represented as
the cardinality of its finite configuration space. -/
noncomputable def switchingMass (T : Finset (V × V))
    (score : Finset V → ℤ) (ℓ x : ℤ) : ℕ :=
  by
    classical
    exact Nat.card (SwitchConfiguration T score ℓ x)

/-- Exact switch reversal, KSSS (4.52), before division by the size of the
uniform sample space. -/
theorem switchingMass_reverse {T : Finset (V × V)}
    {score : Finset V → ℤ} (hT : IsSymmetric T) (ℓ x : ℤ) :
    switchingMass T score ℓ x = switchingMass T score (-ℓ) (x + ℓ) := by
  classical
  exact Nat.card_congr (reverseConfigurationEquiv hT ℓ x)

end ExactSwitch

section RawMoments

variable {Omega : Type u} {I : Type v}

/-- Indicator of a proposition, valued in the reals. -/
noncomputable def indicator (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

lemma indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  classical
  by_cases hp : p <;> simp [indicator, hp]

@[simp] lemma indicator_sq (p : Prop) : indicator p ^ 2 = indicator p := by
  classical
  by_cases hp : p <;> simp [indicator, hp]

/-- A raw (not falling-factorial) mixed moment on a finite sample space.
The exponent function takes values in `ℕ`; Lemma 13.4 uses only `0,1,2`. -/
noncomputable def rawMoment (states : Finset Omega) (event : Omega → Prop)
    (Y : I → Omega → ℝ) (a : I → ℕ) (labels : Finset I) : ℝ :=
  by
    classical
    exact ∑ ω ∈ states, indicator (event ω) * ∏ i ∈ labels, (Y i ω) ^ (a i)

/-- Uniform expectation on an explicitly supplied nonempty finite sample
space.  Keeping the sample space as a `Finset` makes the normalization in
KSSS Lemma 13.4 visible. -/
noncomputable def uniformMeanOn (states : Finset Omega) (f : Omega → ℝ) : ℝ :=
  (∑ ω ∈ states, f ω) / (states.card : ℝ)

/-- The finite sum defining a switching moment is exactly the cardinality
of the corresponding switching-configuration space. -/
theorem sum_switchingCount_indicator_eq_switchingMass
    {V : Type u} [Fintype V]
    (T : Finset (V × V)) (score : Finset V → ℤ) (ℓ x : ℤ) :
    (∑ U : Finset V,
        (switchingCount T score ℓ U : ℝ) * indicator (score U = x)) =
      (switchingMass T score ℓ x : ℝ) := by
  classical
  have hnat :
      (∑ U : Finset V,
          switchingCount T score ℓ U * if score U = x then 1 else 0) =
        switchingMass T score ℓ x := by
    rw [switchingMass, Nat.card_eq_fintype_card]
    change (∑ U : Finset V,
        switchingCount T score ℓ U * if score U = x then 1 else 0) =
      Fintype.card {c : Finset V × (V × V) //
        c.2 ∈ T ∧ c.2.1 ∈ c.1 ∧ c.2.2 ∉ c.1 ∧
          score c.1 = x ∧ switchIncrement score c.1 c.2.1 c.2.2 = ℓ}
    rw [Fintype.card_subtype]
    simp only [switchingCount]
    rw [Finset.card_filter]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hprod (F : Finset V × (V × V) → ℕ) :
        (∑ c, F c) = ∑ U : Finset V, ∑ yz : V × V, F (U, yz) := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    rw [hprod]
    apply Finset.sum_congr rfl
    intro U hU
    by_cases hx : score U = x
    · simp only [hx, if_true]
      have hf :
          T.filter (fun yz ↦ yz.1 ∈ U ∧ yz.2 ∉ U ∧
            switchIncrement score U yz.1 yz.2 = ℓ) =
          (Finset.univ : Finset (V × V)).filter (fun yz ↦
            yz ∈ T ∧ yz.1 ∈ U ∧ yz.2 ∉ U ∧
              True ∧ switchIncrement score U yz.1 yz.2 = ℓ) := by
        ext yz
        simp [and_left_comm]
      have hc := congrArg Finset.card hf
      simpa only [Finset.card_filter, Finset.card_eq_sum_ones,
        Finset.sum_filter, mul_one] using hc
    · simp [hx]
  simp only [indicator]
  exact_mod_cast hnat

/-- Exact switch reversal in normalized finite-expectation form, KSSS
(4.52).  This is the bridge from the graph-specific bijection to the raw
moment Cauchy--Schwarz argument. -/
theorem uniformMeanOn_switching_reversal
    {V : Type u} [Fintype V]
    {T : Finset (V × V)} {score : Finset V → ℤ}
    (hT : IsSymmetric T) (ℓ x : ℤ) :
    uniformMeanOn (Finset.univ : Finset (Finset V))
        (fun U ↦ (switchingCount T score ℓ U : ℝ) *
          indicator (score U = x)) =
      uniformMeanOn (Finset.univ : Finset (Finset V))
        (fun U ↦ (switchingCount T score (-ℓ) U : ℝ) *
          indicator (score U = x + ℓ)) := by
  unfold uniformMeanOn
  rw [sum_switchingCount_indicator_eq_switchingMass,
    sum_switchingCount_indicator_eq_switchingMass,
    switchingMass_reverse hT]

/-- The normalized raw mixed moment appearing in KSSS Lemma 13.4. -/
noncomputable def rawMomentExpectation (states : Finset Omega)
    (event : Omega → Prop) (Y : I → Omega → ℝ)
    (a : I → ℕ) (labels : Finset I) : ℝ :=
  rawMoment states event Y a labels / (states.card : ℝ)

/-! ### Ordered-tuple expansion

The proof of KSSS Lemma 13.4 expands each ordinary power into ordered
tuples of admissible switches.  The following finite definitions make that
expansion exact, including repeated switches and coincident coordinates. -/

/-- One coordinate for each of the `a i` ordered occurrences of every
label `i`. -/
abbrev RawTupleIndex {J : Type u} (labels : Finset J) (a : J → ℕ) :=
  Σ i : {i // i ∈ labels}, Fin (a i.1)

lemma card_rawTupleIndex {J : Type u} [DecidableEq J]
    (labels : Finset J) (a : J → ℕ) :
    Nat.card (RawTupleIndex labels a) = ∑ i ∈ labels, a i := by
  classical
  let : Fintype {i // i ∈ labels} :=
    Fintype.ofFinset labels (fun i ↦ Iff.rfl)
  let : ∀ i : {i // i ∈ labels}, Fintype (Fin (a i.1)) :=
    fun i ↦ Fin.fintype (a i.1)
  let : Fintype (RawTupleIndex labels a) := inferInstance
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_fin]
  exact Finset.sum_finset_coe a labels

/-- Exponents in `{0,1,2}` produce at most twice as many ordered tuple
coordinates as labels.  For the window `[-B,B]` this is `4B+2`. -/
lemma card_rawTupleIndex_le_two_mul {J : Type u} [DecidableEq J]
    (labels : Finset J) (a : J → ℕ)
    (ha : ∀ i ∈ labels, a i ≤ 2) :
    Nat.card (RawTupleIndex labels a) ≤ 2 * labels.card := by
  rw [card_rawTupleIndex]
  calc
    (∑ i ∈ labels, a i) ≤ ∑ _i ∈ labels, 2 :=
      Finset.sum_le_sum fun i hi ↦ ha i hi
    _ = 2 * labels.card := by simp [Nat.mul_comm]

/-- The dependent Cartesian product of the choice sets indexed by the raw
moment exponent vector. -/
noncomputable def rawTupleFinset {J : Type u} {β : Type v}
    [DecidableEq J] [DecidableEq β]
    (labels : Finset J) (a : J → ℕ) (choices : J → Finset β) :
    Finset (RawTupleIndex labels a → β) := by
  classical
  letI : Fintype {i // i ∈ labels} :=
    Fintype.ofFinset labels (fun i ↦ Iff.rfl)
  letI : ∀ i : {i // i ∈ labels}, Fintype (Fin (a i.1)) :=
    fun i ↦ Fin.fintype (a i.1)
  letI : Fintype (RawTupleIndex labels a) := inferInstance
  exact Fintype.piFinset fun j ↦ choices j.1.1

lemma card_rawTupleFinset {J : Type u} {β : Type v}
    [DecidableEq J] [DecidableEq β]
    (labels : Finset J) (a : J → ℕ) (choices : J → Finset β) :
    (rawTupleFinset labels a choices).card =
      ∏ i ∈ labels, (choices i).card ^ (a i) := by
  classical
  let : Fintype {i // i ∈ labels} :=
    Fintype.ofFinset labels (fun i ↦ Iff.rfl)
  let : ∀ i : {i // i ∈ labels}, Fintype (Fin (a i.1)) :=
    fun i ↦ Fin.fintype (a i.1)
  let : Fintype (RawTupleIndex labels a) := inferInstance
  rw [rawTupleFinset, Fintype.card_piFinset]
  rw [Fintype.prod_sigma]
  simp_rw [Fin.prod_const]
  exact Finset.prod_finset_coe (fun i ↦ (choices i).card ^ a i) labels

/-- The admissible ordered switches with a fixed increment at one state. -/
noncomputable def admissibleSwitches {W : Type u} [Fintype W]
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (U : Finset W) (ell : ℤ) : Finset (W × W) := by
  classical
  exact T.filter fun yz ↦ yz.1 ∈ U ∧ yz.2 ∉ U ∧
    switchIncrement score U yz.1 yz.2 = ell

@[simp] lemma card_admissibleSwitches {W : Type u} [Fintype W]
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (U : Finset W) (ell : ℤ) :
    (admissibleSwitches T score U ell).card =
      switchingCount T score ell U := by
  rfl

/-- All ordered switch tuples counted by a raw mixed moment at `U`. -/
noncomputable def switchingTupleFinset {W : Type u} [Fintype W]
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (labels : Finset ℤ) (a : ℤ → ℕ) (U : Finset W) :
    Finset (RawTupleIndex labels a → W × W) := by
  classical
  exact rawTupleFinset labels a (admissibleSwitches T score U)

lemma card_switchingTupleFinset {W : Type u} [Fintype W]
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (labels : Finset ℤ) (a : ℤ → ℕ) (U : Finset W) :
    (switchingTupleFinset T score labels a U).card =
      ∏ ell ∈ labels, (switchingCount T score ell U) ^ (a ell) := by
  classical
  simpa [switchingTupleFinset] using
    card_rawTupleFinset labels a (admissibleSwitches T score U)

/-- Exact expansion of a switching raw moment as a weighted count of
ordered switch tuples. -/
lemma rawMoment_switchingCount_eq_tupleCount {W : Type u} [Fintype W]
    (states : Finset (Finset W)) (event : Finset W → Prop)
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (labels : Finset ℤ) (a : ℤ → ℕ) :
    rawMoment states event
        (fun ell U ↦ (switchingCount T score ell U : ℝ)) a labels =
      ∑ U ∈ states, indicator (event U) *
        ((switchingTupleFinset T score labels a U).card : ℝ) := by
  classical
  unfold rawMoment
  apply Finset.sum_congr rfl
  intro U hU
  congr 1
  rw [card_switchingTupleFinset]
  push_cast
  rfl

/-- Normalized form of `rawMoment_switchingCount_eq_tupleCount`. -/
lemma rawMomentExpectation_switchingCount_eq_tupleCount
    {W : Type u} [Fintype W]
    (states : Finset (Finset W)) (event : Finset W → Prop)
    (T : Finset (W × W)) (score : Finset W → ℤ)
    (labels : Finset ℤ) (a : ℤ → ℕ) :
    rawMomentExpectation states event
        (fun ell U ↦ (switchingCount T score ell U : ℝ)) a labels =
      (∑ U ∈ states, indicator (event U) *
        ((switchingTupleFinset T score labels a U).card : ℝ)) /
          (states.card : ℝ) := by
  rw [rawMomentExpectation, rawMoment_switchingCount_eq_tupleCount]

/-- Exact input shape of the two-sided comparison in KSSS Lemma 13.4.

This is deliberately a predicate, not a proved theorem: its proof is the
remaining graph/probability content of Section 13.  The powers are ordinary
powers and the comparison is required only for exponents `0`, `1`, or `2`.
In the paper, `scale = |T| / √n` and `normalizer = n^(3/2)`. -/
def RawMomentComparison (states : Finset Omega) (event : Omega → Prop)
    (Y : I → Omega → ℝ) (labels : Finset I)
    (scale normalizer lower upper : ℝ) : Prop :=
  0 < scale ∧ 0 < normalizer ∧ 0 < lower ∧ 0 < upper ∧
    ∀ a : I → ℕ, (∀ i ∈ labels, a i ≤ 2) →
      lower * scale ^ (∑ i ∈ labels, a i) / normalizer ≤
          rawMomentExpectation states event Y a labels ∧
        rawMomentExpectation states event Y a labels ≤
          upper * scale ^ (∑ i ∈ labels, a i) / normalizer

/-- Finite averaging step (4.53): if a window moment is the sum of its
point moments, one point carries at least the average mass. -/
lemma exists_pointMoment_ge_window_average [DecidableEq I]
    (labels : Finset I) (hlabels : labels.Nonempty)
    (windowMoment : ℝ) (pointMoment : I → ℝ)
    (hpartition : windowMoment = ∑ i ∈ labels, pointMoment i) :
    ∃ i ∈ labels, windowMoment / (labels.card : ℝ) ≤ pointMoment i := by
  classical
  by_contra h
  push_neg at h
  have hsum :
      (∑ i ∈ labels, pointMoment i) <
        ∑ i ∈ labels, windowMoment / (labels.card : ℝ) :=
    Finset.sum_lt_sum_of_nonempty hlabels fun i hi ↦ h i hi
  have hcard : (labels.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hlabels
  have hconstant :
      (∑ _i ∈ labels, windowMoment / (labels.card : ℝ)) = windowMoment := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [← hpartition, hconstant] at hsum
  exact (lt_irrefl _ hsum)

/-- The product used in the first Cauchy--Schwarz step: all variables are
squared except the selected one, which occurs to the first power. -/
def oneUnsquaredProduct [DecidableEq I] (labels : Finset I) (selected : I)
    (Y : I → Omega → ℝ) (ω : Omega) : ℝ :=
  Y selected ω * ∏ i ∈ labels.erase selected, (Y i ω) ^ 2

/-- Exponent vectors used when Lemma 13.4 is inserted into the first and
second Cauchy--Schwarz steps. -/
def allOneExponent : I → ℕ := fun _ ↦ 1

def oneUnsquaredExponent [DecidableEq I] (selected : I) : I → ℕ :=
  fun i ↦ if i = selected then 1 else 2

def singleSquaredExponent [DecidableEq I] (selected : I) : I → ℕ :=
  fun i ↦ if i = selected then 2 else 0

lemma rawMomentExpectation_allOne (states : Finset Omega)
    (event : Omega → Prop) (Y : I → Omega → ℝ) (labels : Finset I) :
    rawMomentExpectation states event Y allOneExponent labels =
      uniformMeanOn states (fun ω ↦
        (∏ i ∈ labels, Y i ω) * indicator (event ω)) := by
  classical
  simp [rawMomentExpectation, rawMoment, uniformMeanOn, allOneExponent, mul_comm]

lemma rawMomentExpectation_oneUnsquared [DecidableEq I]
    (states : Finset Omega) (event : Omega → Prop)
    (Y : I → Omega → ℝ) (labels : Finset I) {selected : I}
    (hselected : selected ∈ labels) :
    rawMomentExpectation states event Y (oneUnsquaredExponent selected) labels =
      uniformMeanOn states (fun ω ↦
        oneUnsquaredProduct labels selected Y ω * indicator (event ω)) := by
  classical
  apply congrArg (fun x : ℝ ↦ x / (states.card : ℝ))
  apply Finset.sum_congr rfl
  intro ω hω
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hselected]
  rw [Finset.sdiff_singleton_eq_erase]
  have htail :
      (∏ i ∈ labels.erase selected, Y i ω ^ oneUnsquaredExponent selected i) =
        ∏ i ∈ labels.erase selected, Y i ω ^ 2 := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [oneUnsquaredExponent, (Finset.mem_erase.mp hi).1]
  rw [htail]
  simp [rawMoment, oneUnsquaredExponent, oneUnsquaredProduct, mul_comm]

lemma rawMomentExpectation_singleSquared [DecidableEq I]
    (states : Finset Omega) (event : Omega → Prop)
    (Y : I → Omega → ℝ) (labels : Finset I) {selected : I}
    (hselected : selected ∈ labels) :
    rawMomentExpectation states event Y (singleSquaredExponent selected) labels =
      uniformMeanOn states (fun ω ↦
        Y selected ω ^ 2 * indicator (event ω)) := by
  classical
  apply congrArg (fun x : ℝ ↦ x / (states.card : ℝ))
  apply Finset.sum_congr rfl
  intro ω hω
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hselected]
  simp [rawMoment, singleSquaredExponent, Finset.sdiff_singleton_eq_erase, mul_comm]

/-- Pointwise factorization behind the first Cauchy--Schwarz application. -/
lemma product_sq_factorization [DecidableEq I] (labels : Finset I)
    {selected : I} (hselected : selected ∈ labels)
    (Y : I → Omega → ℝ) (ω : Omega) :
    (∏ i ∈ labels, Y i ω) ^ 2 =
      Y selected ω * oneUnsquaredProduct labels selected Y ω := by
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem hselected]
  simp only [oneUnsquaredProduct, Finset.sdiff_singleton_eq_erase,
    mul_pow, Finset.prod_pow]
  ring

/-- First Cauchy--Schwarz step in the switching proof. -/
theorem product_indicator_cauchy_schwarz [DecidableEq I]
    (states : Finset Omega) (labels : Finset I) {selected : I}
    (hselected : selected ∈ labels) (event : Omega → Prop)
    (Y : I → Omega → ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω) :
    (∑ ω ∈ states, (∏ i ∈ labels, Y i ω) * indicator (event ω)) ^ 2 ≤
      (∑ ω ∈ states, Y selected ω * indicator (event ω)) *
        ∑ ω ∈ states,
          oneUnsquaredProduct labels selected Y ω * indicator (event ω) := by
  classical
  let r : Omega → ℝ := fun ω ↦
    (∏ i ∈ labels, Y i ω) * indicator (event ω)
  let f : Omega → ℝ := fun ω ↦ Y selected ω * indicator (event ω)
  let g : Omega → ℝ := fun ω ↦
    oneUnsquaredProduct labels selected Y ω * indicator (event ω)
  have hf : ∀ ω ∈ states, 0 ≤ f ω := by
    intro ω hω
    exact mul_nonneg (hY selected hselected ω hω) (indicator_nonneg _)
  have hg : ∀ ω ∈ states, 0 ≤ g ω := by
    intro ω hω
    refine mul_nonneg (mul_nonneg (hY selected hselected ω hω) ?_)
      (indicator_nonneg _)
    exact Finset.prod_nonneg fun i hi ↦ sq_nonneg _
  have hpoint : ∀ ω ∈ states, r ω ^ 2 ≤ f ω * g ω := by
    intro ω hω
    change ((∏ i ∈ labels, Y i ω) * indicator (event ω)) ^ 2 ≤
      (Y selected ω * indicator (event ω)) *
        (oneUnsquaredProduct labels selected Y ω * indicator (event ω))
    by_cases he : event ω
    · simp only [indicator, he, if_true, mul_one]
      exact (product_sq_factorization labels hselected Y ω).le
    · simp [indicator, he]
  simpa [r, f, g] using
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul states hf hg hpoint

/-- Second Cauchy--Schwarz step: a weighted point mass is controlled by the
point mass itself times its raw second moment. -/
theorem weighted_indicator_cauchy_schwarz (states : Finset Omega)
    (event : Omega → Prop) (Y : Omega → ℝ) :
    (∑ ω ∈ states, Y ω * indicator (event ω)) ^ 2 ≤
      (∑ ω ∈ states, indicator (event ω)) *
        ∑ ω ∈ states, Y ω ^ 2 * indicator (event ω) := by
  classical
  let r : Omega → ℝ := fun ω ↦ Y ω * indicator (event ω)
  let f : Omega → ℝ := fun ω ↦ indicator (event ω)
  let g : Omega → ℝ := fun ω ↦ Y ω ^ 2 * indicator (event ω)
  have hf : ∀ ω ∈ states, 0 ≤ f ω := fun ω _ ↦ indicator_nonneg _
  have hg : ∀ ω ∈ states, 0 ≤ g ω := fun ω _ ↦
    mul_nonneg (sq_nonneg _) (indicator_nonneg _)
  have hpoint : ∀ ω ∈ states, r ω ^ 2 ≤ f ω * g ω := by
    intro ω _
    by_cases he : event ω <;> simp [r, f, g, indicator, he]
  simpa [r, f, g] using
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul states hf hg hpoint

/-- First Cauchy--Schwarz step after dividing every sum by the size of the
same nonempty uniform sample space. -/
theorem uniformMeanOn_product_indicator_cauchy_schwarz [DecidableEq I]
    (states : Finset Omega) (hstates : states.Nonempty)
    (labels : Finset I) {selected : I} (hselected : selected ∈ labels)
    (event : Omega → Prop) (Y : I → Omega → ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω) :
    uniformMeanOn states
        (fun ω ↦ (∏ i ∈ labels, Y i ω) * indicator (event ω)) ^ 2 ≤
      uniformMeanOn states
          (fun ω ↦ Y selected ω * indicator (event ω)) *
        uniformMeanOn states (fun ω ↦
          oneUnsquaredProduct labels selected Y ω * indicator (event ω)) := by
  classical
  have hcard : 0 < (states.card : ℝ) := by
    exact_mod_cast hstates.card_pos
  have h := product_indicator_cauchy_schwarz
    states labels hselected event Y hY
  unfold uniformMeanOn
  calc
    ((∑ ω ∈ states,
          (∏ i ∈ labels, Y i ω) * indicator (event ω)) /
        (states.card : ℝ)) ^ 2 =
        (∑ ω ∈ states,
          (∏ i ∈ labels, Y i ω) * indicator (event ω)) ^ 2 /
            (states.card : ℝ) ^ 2 := by ring
    _ ≤ ((∑ ω ∈ states, Y selected ω * indicator (event ω)) *
          ∑ ω ∈ states,
            oneUnsquaredProduct labels selected Y ω * indicator (event ω)) /
          (states.card : ℝ) ^ 2 := by
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hcard)).2 h
    _ = ((∑ ω ∈ states, Y selected ω * indicator (event ω)) /
          (states.card : ℝ)) *
        ((∑ ω ∈ states,
          oneUnsquaredProduct labels selected Y ω * indicator (event ω)) /
            (states.card : ℝ)) := by ring

/-- Second Cauchy--Schwarz step in normalized expectation form. -/
theorem uniformMeanOn_weighted_indicator_cauchy_schwarz
    (states : Finset Omega) (hstates : states.Nonempty)
    (event : Omega → Prop) (Y : Omega → ℝ) :
    uniformMeanOn states (fun ω ↦ Y ω * indicator (event ω)) ^ 2 ≤
      uniformMeanOn states (fun ω ↦ indicator (event ω)) *
        uniformMeanOn states (fun ω ↦ Y ω ^ 2 * indicator (event ω)) := by
  classical
  have hcard : 0 < (states.card : ℝ) := by
    exact_mod_cast hstates.card_pos
  have h := weighted_indicator_cauchy_schwarz states event Y
  unfold uniformMeanOn
  calc
    ((∑ ω ∈ states, Y ω * indicator (event ω)) /
        (states.card : ℝ)) ^ 2 =
        (∑ ω ∈ states, Y ω * indicator (event ω)) ^ 2 /
          (states.card : ℝ) ^ 2 := by ring
    _ ≤ ((∑ ω ∈ states, indicator (event ω)) *
          ∑ ω ∈ states, Y ω ^ 2 * indicator (event ω)) /
            (states.card : ℝ) ^ 2 := by
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hcard)).2 h
    _ = ((∑ ω ∈ states, indicator (event ω)) /
          (states.card : ℝ)) *
        ((∑ ω ∈ states, Y ω ^ 2 * indicator (event ω)) /
          (states.card : ℝ)) := by ring

/-- The exact algebraic implication used after Lemma 13.4.

`L` is a lower bound for the product moment at the selected window point;
`U` bounds the moment with every factor squared except the reverse-switch
factor; `V` bounds the second moment at the target point.  The equality
`hreversal` is (4.52).  The conclusion is division-free, so it remains valid
at zero and can be combined directly with asymptotic bounds.
-/
theorem raw_moments_force_point_mass [DecidableEq I]
    (states : Finset Omega) (labels : Finset I) {selected reverse : I}
    (hselected : selected ∈ labels) (hreverse : reverse ∈ labels)
    (source target : Omega → Prop)
    (Y : I → Omega → ℝ) (L U V : ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω)
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hlower : L ≤
      ∑ ω ∈ states, (∏ i ∈ labels, Y i ω) * indicator (source ω))
    (hupper :
      (∑ ω ∈ states,
        oneUnsquaredProduct labels reverse Y ω * indicator (source ω)) ≤ U)
    (hreversal :
      (∑ ω ∈ states, Y reverse ω * indicator (source ω)) =
        ∑ ω ∈ states, Y selected ω * indicator (target ω))
    (hsecond :
      (∑ ω ∈ states, Y selected ω ^ 2 * indicator (target ω)) ≤ V) :
    L ^ 4 ≤
      (∑ ω ∈ states, indicator (target ω)) * U ^ 2 * V := by
  classical
  let A : ℝ :=
    ∑ ω ∈ states, (∏ i ∈ labels, Y i ω) * indicator (source ω)
  let M : ℝ :=
    ∑ ω ∈ states, Y selected ω * indicator (target ω)
  let R : ℝ :=
    ∑ ω ∈ states,
      oneUnsquaredProduct labels reverse Y ω * indicator (source ω)
  let P : ℝ := ∑ ω ∈ states, indicator (target ω)
  let Q : ℝ :=
    ∑ ω ∈ states, Y selected ω ^ 2 * indicator (target ω)
  have hA0 : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg
      (Finset.prod_nonneg fun i hi ↦ hY i hi ω hω)
      (indicator_nonneg _)
  have hM0 : 0 ≤ M := by
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg
      (hY selected hselected ω hω)
      (indicator_nonneg _)
  have hR0 : 0 ≤ R := by
    apply Finset.sum_nonneg
    intro ω hω
    exact mul_nonneg
      (mul_nonneg (hY reverse hreverse ω hω)
        (Finset.prod_nonneg fun i hi ↦ sq_nonneg _))
      (indicator_nonneg _)
  have hP0 : 0 ≤ P := by
    exact Finset.sum_nonneg fun _ _ ↦ indicator_nonneg _
  have hQ0 : 0 ≤ Q := by
    exact Finset.sum_nonneg fun _ _ ↦
      mul_nonneg (sq_nonneg _) (indicator_nonneg _)
  have hfirst : A ^ 2 ≤ M * R := by
    have h := product_indicator_cauchy_schwarz states labels hreverse source Y hY
    simpa [A, M, R, hreversal] using h
  have hLMU : L ^ 2 ≤ M * U := by
    calc
      L ^ 2 ≤ A ^ 2 := (sq_le_sq₀ hL hA0).2 hlower
      _ ≤ M * R := hfirst
      _ ≤ M * U := mul_le_mul_of_nonneg_left hupper hM0
  have hsecondCS : M ^ 2 ≤ P * Q := by
    simpa [M, P, Q] using
      weighted_indicator_cauchy_schwarz states target (Y selected)
  calc
    L ^ 4 = (L ^ 2) ^ 2 := by ring
    _ ≤ (M * U) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg L) (mul_nonneg hM0 hU)).2 hLMU
    _ = M ^ 2 * U ^ 2 := by ring
    _ ≤ (P * Q) * U ^ 2 := mul_le_mul_of_nonneg_right hsecondCS (sq_nonneg U)
    _ ≤ (P * V) * U ^ 2 := by
      gcongr
    _ = P * U ^ 2 * V := by ring

/-- Normalized-expectation form of `raw_moments_force_point_mass`.

This is the exact endpoint needed after the ordinary-power comparison input
of Lemma 13.4 and the averaging step (4.53).  Unlike the unnormalized form,
its conclusion is already a lower-bound inequality for the point
probability `E[Z_x]`. -/
theorem normalized_raw_moments_force_point_mass [DecidableEq I]
    (states : Finset Omega) (hstates : states.Nonempty)
    (labels : Finset I) {selected reverse : I}
    (hselected : selected ∈ labels) (hreverse : reverse ∈ labels)
    (source target : Omega → Prop)
    (Y : I → Omega → ℝ) (L U V : ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω)
    (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hlower : L ≤ uniformMeanOn states (fun ω ↦
      (∏ i ∈ labels, Y i ω) * indicator (source ω)))
    (hupper : uniformMeanOn states (fun ω ↦
      oneUnsquaredProduct labels reverse Y ω * indicator (source ω)) ≤ U)
    (hreversal : uniformMeanOn states
        (fun ω ↦ Y reverse ω * indicator (source ω)) =
      uniformMeanOn states
        (fun ω ↦ Y selected ω * indicator (target ω)))
    (hsecond : uniformMeanOn states
        (fun ω ↦ Y selected ω ^ 2 * indicator (target ω)) ≤ V) :
    L ^ 4 ≤ uniformMeanOn states (fun ω ↦ indicator (target ω)) * U ^ 2 * V := by
  classical
  let A : ℝ := uniformMeanOn states (fun ω ↦
    (∏ i ∈ labels, Y i ω) * indicator (source ω))
  let M : ℝ := uniformMeanOn states
    (fun ω ↦ Y selected ω * indicator (target ω))
  let R : ℝ := uniformMeanOn states (fun ω ↦
    oneUnsquaredProduct labels reverse Y ω * indicator (source ω))
  let P : ℝ := uniformMeanOn states (fun ω ↦ indicator (target ω))
  let Q : ℝ := uniformMeanOn states
    (fun ω ↦ Y selected ω ^ 2 * indicator (target ω))
  have hcard : 0 < (states.card : ℝ) := by
    exact_mod_cast hstates.card_pos
  have hA0 : 0 ≤ A := by
    dsimp [A, uniformMeanOn]
    apply div_nonneg
    · exact Finset.sum_nonneg fun ω hω ↦ mul_nonneg
        (Finset.prod_nonneg fun i hi ↦ hY i hi ω hω) (indicator_nonneg _)
    · exact hcard.le
  have hM0 : 0 ≤ M := by
    dsimp [M, uniformMeanOn]
    apply div_nonneg
    · exact Finset.sum_nonneg fun ω hω ↦
        mul_nonneg (hY selected hselected ω hω) (indicator_nonneg _)
    · exact hcard.le
  have hfirst : A ^ 2 ≤ M * R := by
    have h := uniformMeanOn_product_indicator_cauchy_schwarz
      states hstates labels hreverse source Y hY
    simpa [A, M, R, hreversal] using h
  have hLMU : L ^ 2 ≤ M * U := by
    calc
      L ^ 2 ≤ A ^ 2 := (sq_le_sq₀ hL hA0).2 hlower
      _ ≤ M * R := hfirst
      _ ≤ M * U := mul_le_mul_of_nonneg_left hupper hM0
  have hsecondCS : M ^ 2 ≤ P * Q := by
    simpa [M, P, Q] using
      uniformMeanOn_weighted_indicator_cauchy_schwarz
        states hstates target (Y selected)
  have hP0 : 0 ≤ P := by
    dsimp [P, uniformMeanOn]
    apply div_nonneg
    · exact Finset.sum_nonneg fun ω hω ↦ indicator_nonneg _
    · exact hcard.le
  calc
    L ^ 4 = (L ^ 2) ^ 2 := by ring
    _ ≤ (M * U) ^ 2 :=
      (sq_le_sq₀ (sq_nonneg L) (mul_nonneg hM0 hU)).2 hLMU
    _ = M ^ 2 * U ^ 2 := by ring
    _ ≤ (P * Q) * U ^ 2 := mul_le_mul_of_nonneg_right hsecondCS (sq_nonneg U)
    _ ≤ (P * V) * U ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsecond hP0) (sq_nonneg U)
    _ = P * U ^ 2 * V := by ring

/-- Scale cancellation from the four moment bounds used in KSSS
(4.53)--(4.55).  This formulation exposes exactly the lower all-one moment,
the two upper moments, and the reversal identity, so it can be applied after
averaging a bounded window down to one point. -/
theorem scaledRawMomentBounds_force_pointProbability
    [DecidableEq I]
    (states : Finset Omega) (hstates : states.Nonempty)
    (labels : Finset I) (hlabels : labels.Nonempty)
    {selected reverse : I} (hselected : selected ∈ labels)
    (hreverse : reverse ∈ labels)
    (source target : Omega → Prop) (Y : I → Omega → ℝ)
    (scale normalizer lower upper : ℝ)
    (hscale : 0 < scale) (hnormalizer : 0 < normalizer)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω)
    (hall : lower * scale ^ labels.card / normalizer ≤
      uniformMeanOn states (fun ω ↦
        (∏ i ∈ labels, Y i ω) * indicator (source ω)))
    (hunsquared : uniformMeanOn states (fun ω ↦
        oneUnsquaredProduct labels reverse Y ω * indicator (source ω)) ≤
      upper * scale ^ (2 * labels.card - 1) / normalizer)
    (hreversal : uniformMeanOn states
        (fun ω ↦ Y reverse ω * indicator (source ω)) =
      uniformMeanOn states
        (fun ω ↦ Y selected ω * indicator (target ω)))
    (hsquared : uniformMeanOn states
        (fun ω ↦ Y selected ω ^ 2 * indicator (target ω)) ≤
      upper * scale ^ 2 / normalizer) :
    lower ^ 4 / (upper ^ 3 * normalizer) ≤
      uniformMeanOn states (fun ω ↦ indicator (target ω)) := by
  have hforce := normalized_raw_moments_force_point_mass
    states hstates labels hselected hreverse source target Y
    (lower * scale ^ labels.card / normalizer)
    (upper * scale ^ (2 * labels.card - 1) / normalizer)
    (upper * scale ^ 2 / normalizer) hY
    (by positivity) (by positivity) hall hunsquared hreversal hsquared
  let P : ℝ := uniformMeanOn states (fun ω ↦ indicator (target ω))
  have hscalePow :
      (scale ^ (2 * labels.card - 1)) ^ 2 * scale ^ 2 =
        scale ^ (4 * labels.card) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    have hD : 1 ≤ labels.card := Finset.one_le_card.mpr hlabels
    omega
  have hleft :
      (lower * scale ^ labels.card / normalizer) ^ 4 =
        lower ^ 4 * scale ^ (4 * labels.card) / normalizer ^ 4 := by
    have hs : (scale ^ labels.card) ^ 4 = scale ^ (4 * labels.card) := by
      calc
        (scale ^ labels.card) ^ 4 = scale ^ (labels.card * 4) :=
          (pow_mul scale labels.card 4).symm
        _ = scale ^ (4 * labels.card) := by congr 1 <;> omega
    rw [div_pow, mul_pow, hs]
  have hright :
      (upper * scale ^ (2 * labels.card - 1) / normalizer) ^ 2 *
          (upper * scale ^ 2 / normalizer) =
        upper ^ 3 * scale ^ (4 * labels.card) / normalizer ^ 3 := by
    rw [div_pow, mul_pow]
    calc
      upper ^ 2 * (scale ^ (2 * labels.card - 1)) ^ 2 / normalizer ^ 2 *
          (upper * scale ^ 2 / normalizer) =
        upper ^ 3 * ((scale ^ (2 * labels.card - 1)) ^ 2 * scale ^ 2) /
          normalizer ^ 3 := by ring
      _ = upper ^ 3 * scale ^ (4 * labels.card) / normalizer ^ 3 := by
        rw [hscalePow]
  have hforce' :
      lower ^ 4 * scale ^ (4 * labels.card) / normalizer ^ 4 ≤
        P * ((upper * scale ^ (2 * labels.card - 1) / normalizer) ^ 2 *
          (upper * scale ^ 2 / normalizer)) := by
    simpa [P, hleft, mul_assoc] using hforce
  rw [hright] at hforce'
  have hscalePowPos : 0 < scale ^ (4 * labels.card) := pow_pos hscale _
  have hnormalizerNe : normalizer ≠ 0 := ne_of_gt hnormalizer
  have hcancel : lower ^ 4 ≤ P * upper ^ 3 * normalizer := by
    have hmul := mul_le_mul_of_nonneg_right hforce'
      (show 0 ≤ normalizer ^ 4 / scale ^ (4 * labels.card) by positivity)
    field_simp [hnormalizerNe, ne_of_gt hscalePowPos] at hmul
    simpa [P, mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [div_le_iff₀ (mul_pos (pow_pos hupper 3) hnormalizer)]
  simpa [P, mul_assoc, mul_left_comm, mul_comm] using hcancel

lemma indicator_mono {p q : Prop} (h : p → q) : indicator p ≤ indicator q := by
  classical
  by_cases hp : p
  · simp [indicator, hp, h hp]
  · by_cases hq : q <;> simp [indicator, hp, hq]

lemma uniformMeanOn_mono (states : Finset Omega)
    {f g : Omega → ℝ} (h : ∀ ω ∈ states, f ω ≤ g ω) :
    uniformMeanOn states f ≤ uniformMeanOn states g := by
  unfold uniformMeanOn
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum fun ω hω ↦ h ω hω
  · positivity

/-- KSSS (4.53)--(4.55), with the bounded-window averaging step exposed.

The raw comparison is required only for the window event.  The point events
partition that window, so one point supplies the all-one lower moment; their
upper moments follow by monotonicity.  Exact reversal then transfers its
one-unsquared factor to the fixed target point. -/
theorem windowRawMomentComparison_force_pointProbability
    [DecidableEq I]
    (states : Finset Omega) (hstates : states.Nonempty)
    (labels : Finset I) (hlabels : labels.Nonempty)
    (point : I → Omega → Prop) (window target : Omega → Prop)
    (reverseLabel : I → I) (Y : I → Omega → ℝ)
    (scale normalizer lower upper : ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω)
    (hwindow : RawMomentComparison states window Y labels
      scale normalizer lower upper)
    (hpartition : ∀ ω ∈ states,
      indicator (window ω) =
        ∑ i ∈ labels, indicator (point i ω))
    (hpointWindow : ∀ i ∈ labels, ∀ ω, point i ω → window ω)
    (htargetWindow : ∀ ω, target ω → window ω)
    (hreverseMem : ∀ i ∈ labels, reverseLabel i ∈ labels)
    (hreversal : ∀ i ∈ labels,
      uniformMeanOn states
          (fun ω ↦ Y (reverseLabel i) ω * indicator (point i ω)) =
        uniformMeanOn states
          (fun ω ↦ Y i ω * indicator (target ω))) :
    (lower / (labels.card : ℝ)) ^ 4 /
        (upper ^ 3 * normalizer) ≤
      uniformMeanOn states (fun ω ↦ indicator (target ω)) := by
  classical
  rcases hwindow with ⟨hscale, hnormalizer, hlower, hupper, hwindow⟩
  let W : ℝ := uniformMeanOn states (fun ω ↦
    (∏ i ∈ labels, Y i ω) * indicator (window ω))
  let Pm : I → ℝ := fun i ↦ uniformMeanOn states (fun ω ↦
    (∏ j ∈ labels, Y j ω) * indicator (point i ω))
  have hmeanPartition : W = ∑ i ∈ labels, Pm i := by
    dsimp only [W, Pm, uniformMeanOn]
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω hω
    calc
      (∏ i ∈ labels, Y i ω) * indicator (window ω) =
          (∏ i ∈ labels, Y i ω) *
            (∑ j ∈ labels, indicator (point j ω)) := by
        rw [hpartition ω hω]
      _ = ∑ j ∈ labels,
          (∏ i ∈ labels, Y i ω) * indicator (point j ω) := by
        rw [Finset.mul_sum]
  have hsumAll : (∑ i ∈ labels, allOneExponent i) = labels.card := by
    simp [allOneExponent]
  have hallWindow : lower * scale ^ labels.card / normalizer ≤ W := by
    have hall := (hwindow allOneExponent (by
      intro i hi
      simp [allOneExponent])).1
    rw [hsumAll, rawMomentExpectation_allOne] at hall
    simpa only [W] using hall
  obtain ⟨selected, hselected, hselectedAverage⟩ :=
    exists_pointMoment_ge_window_average labels hlabels W Pm hmeanPartition
  have hcardPos : 0 < (labels.card : ℝ) := by
    exact_mod_cast hlabels.card_pos
  have hallSelected :
      (lower / (labels.card : ℝ)) * scale ^ labels.card / normalizer ≤
        uniformMeanOn states (fun ω ↦
          (∏ i ∈ labels, Y i ω) * indicator (point selected ω)) := by
    calc
      (lower / (labels.card : ℝ)) * scale ^ labels.card / normalizer =
          (lower * scale ^ labels.card / normalizer) /
            (labels.card : ℝ) := by field_simp
      _ ≤ W / (labels.card : ℝ) :=
        div_le_div_of_nonneg_right hallWindow hcardPos.le
      _ ≤ Pm selected := hselectedAverage
      _ = _ := rfl
  let reverse : I := reverseLabel selected
  have hreverse : reverse ∈ labels := hreverseMem selected hselected
  have hsumUnsquared :
      (∑ i ∈ labels, oneUnsquaredExponent reverse i) =
        2 * labels.card - 1 := by
    calc
      (∑ i ∈ labels, oneUnsquaredExponent reverse i) =
          1 + ∑ i ∈ labels.erase reverse,
            oneUnsquaredExponent reverse i := by
        rw [← Finset.sum_erase_add labels (oneUnsquaredExponent reverse) hreverse]
        simp [oneUnsquaredExponent, add_comm]
      _ = 1 + ∑ _i ∈ labels.erase reverse, 2 := by
        apply congrArg (fun x : ℕ ↦ 1 + x)
        apply Finset.sum_congr rfl
        intro i hi
        simp [oneUnsquaredExponent, (Finset.mem_erase.mp hi).1]
      _ = 2 * labels.card - 1 := by
        simp [Finset.card_erase_of_mem hreverse]
        have hD : 1 ≤ labels.card := Finset.one_le_card.mpr hlabels
        omega
  have hunsquaredWindow :
      uniformMeanOn states (fun ω ↦
          oneUnsquaredProduct labels reverse Y ω * indicator (window ω)) ≤
        upper * scale ^ (2 * labels.card - 1) / normalizer := by
    have hu := (hwindow (oneUnsquaredExponent reverse) (by
      intro i hi
      simp only [oneUnsquaredExponent]
      split <;> omega)).2
    rw [hsumUnsquared,
      rawMomentExpectation_oneUnsquared states window Y labels hreverse] at hu
    exact hu
  have hunsquaredPoint :
      uniformMeanOn states (fun ω ↦
          oneUnsquaredProduct labels reverse Y ω *
            indicator (point selected ω)) ≤
        upper * scale ^ (2 * labels.card - 1) / normalizer := by
    refine (uniformMeanOn_mono states ?_).trans hunsquaredWindow
    intro ω hω
    apply mul_le_mul_of_nonneg_left
    · exact indicator_mono (hpointWindow selected hselected ω)
    · exact mul_nonneg (hY reverse hreverse ω hω)
        (Finset.prod_nonneg fun i hi ↦ sq_nonneg (Y i ω))
  have hsumSquared :
      (∑ i ∈ labels, singleSquaredExponent selected i) = 2 := by
    have htailzero :
        (∑ i ∈ labels.erase selected, singleSquaredExponent selected i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [singleSquaredExponent, (Finset.mem_erase.mp hi).1]
    calc
      (∑ i ∈ labels, singleSquaredExponent selected i) =
          (∑ i ∈ labels.erase selected, singleSquaredExponent selected i) +
            singleSquaredExponent selected selected :=
        (Finset.sum_erase_add labels (singleSquaredExponent selected) hselected).symm
      _ = 0 + 2 := by rw [htailzero]; simp [singleSquaredExponent]
      _ = 2 := by omega
  have hsquaredWindow :
      uniformMeanOn states (fun ω ↦
          Y selected ω ^ 2 * indicator (window ω)) ≤
        upper * scale ^ 2 / normalizer := by
    have hs := (hwindow (singleSquaredExponent selected) (by
      intro i hi
      simp only [singleSquaredExponent]
      split <;> omega)).2
    rw [hsumSquared,
      rawMomentExpectation_singleSquared states window Y labels hselected] at hs
    exact hs
  have hsquaredTarget :
      uniformMeanOn states (fun ω ↦
          Y selected ω ^ 2 * indicator (target ω)) ≤
        upper * scale ^ 2 / normalizer := by
    refine (uniformMeanOn_mono states ?_).trans hsquaredWindow
    intro ω hω
    exact mul_le_mul_of_nonneg_left (indicator_mono (htargetWindow ω))
      (sq_nonneg (Y selected ω))
  apply scaledRawMomentBounds_force_pointProbability
    states hstates labels hlabels hselected hreverse
    (point selected) target Y scale normalizer
    (lower / (labels.card : ℝ)) upper
  · exact hscale
  · exact hnormalizer
  · exact div_pos hlower hcardPos
  · exact hupper
  · exact hY
  · exact hallSelected
  · exact hunsquaredPoint
  · simpa only [reverse] using hreversal selected hselected
  · exact hsquaredTarget

/-- The exact scale-cancellation endpoint of KSSS Section 13.

If the source and target point events satisfy the same raw-moment
comparison and one switching label reverses the source event to the target
event, the normalized target point mass is bounded below by
`lower^4 / (upper^3 * normalizer)`.  In the graph application the scale
powers cancel completely, while `normalizer = n^(3/2)`. -/
theorem rawMomentComparisons_force_pointProbability
    [DecidableEq I]
    (states : Finset Omega) (hstates : states.Nonempty)
    (labels : Finset I) (hlabels : labels.Nonempty)
    {selected reverse : I} (hselected : selected ∈ labels)
    (hreverse : reverse ∈ labels)
    (source target : Omega → Prop) (Y : I → Omega → ℝ)
    (scale normalizer lower upper : ℝ)
    (hY : ∀ i ∈ labels, ∀ ω ∈ states, 0 ≤ Y i ω)
    (hsource : RawMomentComparison states source Y labels
      scale normalizer lower upper)
    (htarget : RawMomentComparison states target Y labels
      scale normalizer lower upper)
    (hreversal : uniformMeanOn states
        (fun ω ↦ Y reverse ω * indicator (source ω)) =
      uniformMeanOn states
        (fun ω ↦ Y selected ω * indicator (target ω))) :
    lower ^ 4 / (upper ^ 3 * normalizer) ≤
      uniformMeanOn states (fun ω ↦ indicator (target ω)) := by
  rcases hsource with ⟨hscale, hnormalizer, hlower, hupper, hsource⟩
  rcases htarget with ⟨_hscale', _hnormalizer', _hlower', _hupper', htarget⟩
  have hD : 1 ≤ labels.card := Finset.one_le_card.mpr hlabels
  have hsumAll : (∑ i ∈ labels, allOneExponent i) = labels.card := by
    simp [allOneExponent]
  have hsumUnsquared :
      (∑ i ∈ labels, oneUnsquaredExponent reverse i) =
        2 * labels.card - 1 := by
    calc
      (∑ i ∈ labels, oneUnsquaredExponent reverse i) =
          1 + ∑ i ∈ labels.erase reverse,
            oneUnsquaredExponent reverse i := by
        rw [← Finset.sum_erase_add labels (oneUnsquaredExponent reverse) hreverse]
        simp [oneUnsquaredExponent, add_comm]
      _ = 1 + ∑ _i ∈ labels.erase reverse, 2 := by
        apply congrArg (fun x : ℕ ↦ 1 + x)
        apply Finset.sum_congr rfl
        intro i hi
        simp [oneUnsquaredExponent, (Finset.mem_erase.mp hi).1]
      _ = 2 * labels.card - 1 := by
        simp [Finset.card_erase_of_mem hreverse]
        omega
  have hsumSquared :
      (∑ i ∈ labels, singleSquaredExponent selected i) = 2 := by
    have htailzero :
        (∑ i ∈ labels.erase selected, singleSquaredExponent selected i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [singleSquaredExponent, (Finset.mem_erase.mp hi).1]
    calc
      (∑ i ∈ labels, singleSquaredExponent selected i) =
          (∑ i ∈ labels.erase selected, singleSquaredExponent selected i) +
            singleSquaredExponent selected selected :=
        (Finset.sum_erase_add labels (singleSquaredExponent selected) hselected).symm
      _ = 0 + 2 := by rw [htailzero]; simp [singleSquaredExponent]
      _ = 2 := by omega
  have hall := (hsource allOneExponent (by
    intro i hi
    simp [allOneExponent])).1
  have hunsquared := (hsource (oneUnsquaredExponent reverse) (by
    intro i hi
    simp only [oneUnsquaredExponent]
    split <;> omega)).2
  have hsquared := (htarget (singleSquaredExponent selected) (by
    intro i hi
    simp only [singleSquaredExponent]
    split <;> omega)).2
  rw [hsumAll, rawMomentExpectation_allOne] at hall
  rw [hsumUnsquared,
    rawMomentExpectation_oneUnsquared states source Y labels hreverse] at hunsquared
  rw [hsumSquared,
    rawMomentExpectation_singleSquared states target Y labels hselected] at hsquared
  have hforce := normalized_raw_moments_force_point_mass
    states hstates labels hselected hreverse source target Y
    (lower * scale ^ labels.card / normalizer)
    (upper * scale ^ (2 * labels.card - 1) / normalizer)
    (upper * scale ^ 2 / normalizer) hY
    (by positivity) (by positivity) hall hunsquared hreversal hsquared
  let P : ℝ := uniformMeanOn states (fun ω ↦ indicator (target ω))
  have hscalePow :
      (scale ^ (2 * labels.card - 1)) ^ 2 * scale ^ 2 =
        scale ^ (4 * labels.card) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hleft :
      (lower * scale ^ labels.card / normalizer) ^ 4 =
        lower ^ 4 * scale ^ (4 * labels.card) / normalizer ^ 4 := by
    have hs : (scale ^ labels.card) ^ 4 = scale ^ (4 * labels.card) := by
      calc
        (scale ^ labels.card) ^ 4 = scale ^ (labels.card * 4) :=
          (pow_mul scale labels.card 4).symm
        _ = scale ^ (4 * labels.card) := by congr 1 <;> omega
    rw [div_pow, mul_pow, hs]
  have hright :
      (upper * scale ^ (2 * labels.card - 1) / normalizer) ^ 2 *
          (upper * scale ^ 2 / normalizer) =
        upper ^ 3 * scale ^ (4 * labels.card) / normalizer ^ 3 := by
    rw [div_pow, mul_pow]
    calc
      upper ^ 2 * (scale ^ (2 * labels.card - 1)) ^ 2 / normalizer ^ 2 *
          (upper * scale ^ 2 / normalizer) =
        upper ^ 3 * ((scale ^ (2 * labels.card - 1)) ^ 2 * scale ^ 2) /
          normalizer ^ 3 := by ring
      _ = upper ^ 3 * scale ^ (4 * labels.card) / normalizer ^ 3 := by
        rw [hscalePow]
  have hforce' :
      lower ^ 4 * scale ^ (4 * labels.card) / normalizer ^ 4 ≤
        P * ((upper * scale ^ (2 * labels.card - 1) / normalizer) ^ 2 *
          (upper * scale ^ 2 / normalizer)) := by
    simpa [P, hleft, mul_assoc] using hforce
  rw [hright] at hforce'
  have hscalePowPos : 0 < scale ^ (4 * labels.card) := pow_pos hscale _
  have hnormalizerNe : normalizer ≠ 0 := ne_of_gt hnormalizer
  have hupperNe : upper ≠ 0 := ne_of_gt hupper
  have hcancel : lower ^ 4 ≤ P * upper ^ 3 * normalizer := by
    have hmul := mul_le_mul_of_nonneg_right hforce'
      (show 0 ≤ normalizer ^ 4 / scale ^ (4 * labels.card) by positivity)
    field_simp [hnormalizerNe, ne_of_gt hscalePowPos] at hmul
    simpa [P, mul_assoc, mul_left_comm, mul_comm] using hmul
  rw [div_le_iff₀ (mul_pos (pow_pos hupper 3) hnormalizer)]
  simpa [P, mul_assoc, mul_left_comm, mul_comm] using hcancel

end RawMoments

end Switching
end Erdos88
