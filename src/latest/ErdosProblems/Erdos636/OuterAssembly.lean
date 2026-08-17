/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos636.ProfileReduction

/-!
# The finite outer assembly for Erdős Problem 636

This file packages the part of the Kwan--Sudakov argument after the
structural and augmentation estimates have been established.  It records
three points which are easy to lose in an asymptotic paper proof:

* the deletion and augmentation sizes use natural-number floors;
* the augmentation parameter may depend on the outer parameter, so the
  resulting order has fibres of size at most `2 * K`, rather than two;
* switching produces separated edge-count windows, whose finite unions have
  exactly the sum of their cardinalities.

The definitions are generic in the ambient objects and in their fixed-order
spectra.  Thus this file can be imported by the main problem file without a
dependency cycle; there one takes `spectra n G k = edgeProfilesAt G k`.
-/

open scoped BigOperators

namespace Erdos636.OuterAssembly

/-! ## Exact rounded parameters -/

/-- The number `f = floor (c₀ n)` of vertices deleted in an outer step. -/
noncomputable def deletionSize (c₀ : ℝ) (n : ℕ) : ℕ :=
  ⌊c₀ * (n : ℝ)⌋₊

/-- The augmentation size `floor (δ₀ sqrt(f) / k)`. -/
noncomputable def augmentationSize (δ₀ : ℝ) (f k : ℕ) : ℕ :=
  ⌊δ₀ * Real.sqrt f / (k : ℝ)⌋₊

/-- The bounded offset `nW + k * floor (δ₀ sqrt(f) / k)`. -/
noncomputable def assemblyOffset (cW c₀ δ₀ : ℝ) (n k : ℕ) : ℕ :=
  ⌊cW * (n : ℝ)⌋₊ + k * augmentationSize δ₀ (deletionSize c₀ n) k

/-- All offsets which can result from a structural parameter `1 ≤ k ≤ K`. -/
noncomputable def offsetSet (cW c₀ δ₀ : ℝ) (n K : ℕ) : Finset ℕ :=
  (Finset.range K).image fun j ↦ assemblyOffset cW c₀ δ₀ n (j + 1)

lemma deletionSize_cast_le {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (n : ℕ) :
    (deletionSize c₀ n : ℝ) ≤ c₀ * n := by
  exact Nat.floor_le (mul_nonneg hc₀ (Nat.cast_nonneg n))

lemma augmentationSize_cast_le {δ₀ : ℝ} (hδ₀ : 0 ≤ δ₀) (f k : ℕ) :
    (augmentationSize δ₀ f k : ℝ) ≤ δ₀ * Real.sqrt f / k := by
  exact Nat.floor_le (div_nonneg (mul_nonneg hδ₀ (Real.sqrt_nonneg _))
    (Nat.cast_nonneg k))

/-- A floor loses less than one.  The weak form is convenient in subsequent
constant calculations. -/
lemma sub_one_le_augmentationSize {δ₀ : ℝ} (f k : ℕ) :
    δ₀ * Real.sqrt f / k - 1 ≤ (augmentationSize δ₀ f k : ℝ) := by
  have h := Nat.lt_floor_add_one (δ₀ * Real.sqrt f / (k : ℝ))
  dsimp [augmentationSize]
  linarith

lemma card_offsetSet_le (cW c₀ δ₀ : ℝ) (n K : ℕ) :
    (offsetSet cW c₀ δ₀ n K).card ≤ K := by
  rw [offsetSet]
  exact (Finset.card_image_le.trans_eq (Finset.card_range K))

lemma assemblyOffset_mem_offsetSet (cW c₀ δ₀ : ℝ) (n K k : ℕ)
    (hk0 : 1 ≤ k) (hkK : k ≤ K) :
    assemblyOffset cW c₀ δ₀ n k ∈ offsetSet cW c₀ δ₀ n K := by
  rw [offsetSet, Finset.mem_image]
  refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
  congr 1
  omega

/-! ## Disjoint switching windows -/

/-- A finite family of edge-count sets, each confined to a real window.
The centres are separated by more than twice the common radius. -/
structure SeparatedWindows (spectrum : Finset ℕ) where
  index : Finset ℕ
  piece : ℕ → Finset ℕ
  center : ℕ → ℝ
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  separated : ∀ i ∈ index, ∀ j ∈ index, i ≠ j →
    center i + 2 * radius < center j ∨ center j + 2 * radius < center i
  in_window : ∀ i ∈ index, ∀ e ∈ piece i, |(e : ℝ) - center i| ≤ radius
  piece_subset : ∀ i ∈ index, piece i ⊆ spectrum

lemma SeparatedWindows.pairwiseDisjoint {spectrum : Finset ℕ}
    (W : SeparatedWindows spectrum) :
    (W.index : Set ℕ).PairwiseDisjoint W.piece := by
  intro i hi j hj hij
  change Disjoint (W.piece i) (W.piece j)
  rw [Finset.disjoint_left]
  intro e hei hej
  have hwi := W.in_window i (by simpa using hi) e hei
  have hwj := W.in_window j (by simpa using hj) e hej
  rcases W.separated i (by simpa using hi) j (by simpa using hj) hij with h | h
  · rw [abs_le] at hwi hwj
    linarith
  · rw [abs_le] at hwi hwj
    linarith

lemma SeparatedWindows.biUnion_subset {spectrum : Finset ℕ}
    (W : SeparatedWindows spectrum) :
    W.index.biUnion W.piece ⊆ spectrum := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨i, hi, hei⟩
  exact W.piece_subset i hi hei

/-- Separated windows contribute the sum of their individual cardinalities
to the ambient fixed-order spectrum. -/
lemma SeparatedWindows.sum_card_le {spectrum : Finset ℕ}
    (W : SeparatedWindows spectrum) :
    ∑ i ∈ W.index, (W.piece i).card ≤ spectrum.card := by
  calc
    ∑ i ∈ W.index, (W.piece i).card =
        (W.index.biUnion W.piece).card :=
      (Finset.card_biUnion W.pairwiseDisjoint).symm
    _ ≤ spectrum.card := Finset.card_le_card W.biUnion_subset

/-- Quantitative switching consequence: `b sqrt(n)` disjoint windows, each
containing `d n` edge counts, yield `b d n sqrt(n)` distinct edge counts at
the fixed order. -/
lemma SeparatedWindows.large_spectrum {spectrum : Finset ℕ}
    (W : SeparatedWindows spectrum) (n : ℕ) (b d : ℝ)
    (_hb : 0 ≤ b) (hd : 0 ≤ d)
    (hindex : b * Real.sqrt n ≤ (W.index.card : ℝ))
    (hpiece : ∀ i ∈ W.index, d * n ≤ ((W.piece i).card : ℝ)) :
    (b * d) * n * Real.sqrt n ≤ (spectrum.card : ℝ) := by
  have hdn : 0 ≤ d * (n : ℝ) := mul_nonneg hd (Nat.cast_nonneg n)
  have hsum :
      ∑ i ∈ W.index, d * (n : ℝ) ≤
        ∑ i ∈ W.index, ((W.piece i).card : ℝ) :=
    Finset.sum_le_sum hpiece
  have hcard :
      (∑ i ∈ W.index, ((W.piece i).card : ℝ)) ≤
        (spectrum.card : ℝ) := by
    exact_mod_cast W.sum_card_le
  calc
    (b * d) * (n : ℝ) * Real.sqrt n =
        (b * Real.sqrt n) * (d * n) := by ring
    _ ≤ (W.index.card : ℝ) * (d * n) :=
      mul_le_mul_of_nonneg_right hindex hdn
    _ = ∑ _i ∈ W.index, d * n := by simp
    _ ≤ ∑ i ∈ W.index, ((W.piece i).card : ℝ) := hsum
    _ ≤ (spectrum.card : ℝ) := hcard

/-! ## The corrected bounded-multiplicity interface -/

/-- Pointwise output of the outer Kwan--Sudakov construction.  The choices
`k ell` and `branch ell` are allowed to depend on `ell`.  The order is
nevertheless one of the two affine orders with an offset in a set of at most
`K` elements. -/
structure RoundedAssemblyInput {E : Type*} (n K : ℕ)
    (cW c₀ δ₀ c a : ℝ) (spectra : ℕ → Finset E) where
  parameter : Finset ℕ
  k : ℕ → ℕ
  branch : ℕ → Bool
  linear_card : c * n ≤ (parameter.card : ℝ)
  deletion_le : ∀ ell ∈ parameter, deletionSize c₀ n ≤ ell
  k_pos : ∀ ell ∈ parameter, 1 ≤ k ell
  k_le : ∀ ell ∈ parameter, k ell ≤ K
  large : ∀ ell ∈ parameter,
    a * n * Real.sqrt n ≤
      ((spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun ell ↦ assemblyOffset cW c₀ δ₀ n (k ell)) branch ell)).card : ℝ)

/-- Build the rounded assembly interface directly from the separated windows
produced by the two switching arguments.  This is where disjointness of the
edge intervals becomes the `n * sqrt n` lower bound used by the profile
reduction. -/
noncomputable def roundedAssemblyInputOfSeparatedWindows
    {n K : ℕ} {cW c₀ δ₀ c b d : ℝ} {spectra : ℕ → Finset ℕ}
    (parameter : Finset ℕ) (k : ℕ → ℕ) (branch : ℕ → Bool)
    (hlinear : c * n ≤ (parameter.card : ℝ))
    (hdeletion : ∀ ell ∈ parameter, deletionSize c₀ n ≤ ell)
    (hkpos : ∀ ell ∈ parameter, 1 ≤ k ell)
    (hkle : ∀ ell ∈ parameter, k ell ≤ K)
    (windows : ∀ ell, SeparatedWindows
      (spectra (ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
        (fun ell ↦ assemblyOffset cW c₀ δ₀ n (k ell)) branch ell)))
    (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hindex : ∀ ell ∈ parameter,
      b * Real.sqrt n ≤ ((windows ell).index.card : ℝ))
    (hpiece : ∀ ell ∈ parameter, ∀ i ∈ (windows ell).index,
      d * n ≤ (((windows ell).piece i).card : ℝ)) :
    RoundedAssemblyInput n K cW c₀ δ₀ c (b * d) spectra where
  parameter := parameter
  k := k
  branch := branch
  linear_card := hlinear
  deletion_le := hdeletion
  k_pos := hkpos
  k_le := hkle
  large := fun ell hell ↦
    (windows ell).large_spectrum n b d hb hd (hindex ell hell)
      (hpiece ell hell)

/-- The finite conclusion needed before summing fixed-order spectra. -/
structure BoundedMultiplicitySpectraData {E : Type*} (n M : ℕ)
    (c a : ℝ) (spectra : ℕ → Finset E) where
  parameter : Finset ℕ
  order : ℕ → ℕ
  multiplicity_pos : 0 < M
  linear_card : c * n ≤ (parameter.card : ℝ)
  fiber_bound : ∀ q ∈ parameter.image order,
    (ProfileReduction.orderFiber parameter order q).card ≤ M
  large : ∀ ell ∈ parameter,
    a * n * Real.sqrt n ≤ ((spectra (order ell)).card : ℝ)

/-- Pointwise final counting consequence of bounded multiplicity.  In the
graph application `profiles` is the set of all induced profiles, and the
containment follows because every tagged fixed-order edge spectrum is an
induced profile slice. -/
lemma BoundedMultiplicitySpectraData.globalProfiles_bound
    {E : Type*} [DecidableEq E] {n M : ℕ} {c a : ℝ}
    {spectra : ℕ → Finset E} (D : BoundedMultiplicitySpectraData n M c a spectra)
    (profiles : Finset (ℕ × E)) (ha : 0 ≤ a)
    (hprofiles : ProfileReduction.taggedSpectra
      (D.parameter.image D.order) spectra ⊆ profiles) :
    (c * a / M) * (n : ℝ) ^ 2 * Real.sqrt n ≤
      (profiles.card : ℝ) := by
  exact ProfileReduction.fiberBound_quadraticSqrt_bound n c a D.parameter
    D.order spectra profiles M ha D.multiplicity_pos
      D.linear_card D.fiber_bound D.large hprofiles

/-- The rounding-correct outer assembly has order multiplicity at most
`2 * K`. -/
noncomputable def RoundedAssemblyInput.toBoundedMultiplicity
    {E : Type*} {n K : ℕ} {cW c₀ δ₀ c a : ℝ}
    {spectra : ℕ → Finset E} (A : RoundedAssemblyInput n K cW c₀ δ₀ c a spectra)
    (hK : 0 < K) : BoundedMultiplicitySpectraData n (2 * K) c a spectra where
  parameter := A.parameter
  order := ProfileReduction.selectedOffsetOrder (deletionSize c₀ n)
    (fun ell ↦ assemblyOffset cW c₀ δ₀ n (A.k ell)) A.branch
  multiplicity_pos := by omega
  linear_card := A.linear_card
  fiber_bound := ProfileReduction.selectedOffsetOrder_fiberBound
    A.parameter (offsetSet cW c₀ δ₀ n K) K (deletionSize c₀ n)
      (fun ell ↦ assemblyOffset cW c₀ δ₀ n (A.k ell)) A.branch
      (card_offsetSet_le cW c₀ δ₀ n K) A.deletion_le
      (fun ell hell ↦ assemblyOffset_mem_offsetSet cW c₀ δ₀ n K (A.k ell)
        (A.k_pos ell hell) (A.k_le ell hell))
  large := A.large

universe u v

/-- Uniform availability of the rounded outer assembly for all sufficiently
large good ambient objects. -/
def HasRoundedAssembly {Ambient : ℕ → Type u} {E : Type v}
    (Good : (n : ℕ) → Ambient n → Prop)
    (spectra : (n : ℕ) → Ambient n → ℕ → Finset E) : Prop :=
  ∃ cW c₀ δ₀ c a : ℝ, 0 < c₀ ∧ 0 < δ₀ ∧ 0 < c ∧ 0 < a ∧
    ∃ K : ℕ, 0 < K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ G : Ambient n, Good n G →
      Nonempty (RoundedAssemblyInput n K cW c₀ δ₀ c a (spectra n G))

/-- Uniform bounded-multiplicity fixed-order spectra.  This is the exact
interface consumed by the final profile-count reduction. -/
def HasBoundedMultiplicitySpectra {Ambient : ℕ → Type u} {E : Type v}
    (Good : (n : ℕ) → Ambient n → Prop)
    (spectra : (n : ℕ) → Ambient n → ℕ → Finset E) : Prop :=
  ∃ c a : ℝ, 0 < c ∧ 0 < a ∧ ∃ M : ℕ, 0 < M ∧
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : Ambient n, Good n G →
      Nonempty (BoundedMultiplicitySpectraData n M c a (spectra n G))

/-- The fully proved finite passage from the rounded structural/augmentation
output to bounded-multiplicity fixed-order spectra. -/
theorem hasBoundedMultiplicitySpectra_of_hasRoundedAssembly
    {Ambient : ℕ → Type u} {E : Type v}
    {Good : (n : ℕ) → Ambient n → Prop}
    {spectra : (n : ℕ) → Ambient n → ℕ → Finset E}
    (h : HasRoundedAssembly Good spectra) :
    HasBoundedMultiplicitySpectra Good spectra := by
  rcases h with ⟨cW, c₀, δ₀, c, a, hc₀, hδ₀, hc, ha, K, hK, N, hN⟩
  refine ⟨c, a, hc, ha, 2 * K, by omega, N, ?_⟩
  intro n hn G hG
  rcases hN n hn G hG with ⟨A⟩
  exact ⟨A.toBoundedMultiplicity hK⟩

/-- Uniform final counting theorem.  Once every tagged fixed-order spectrum
is contained in a chosen global profile set, bounded-multiplicity spectra
give the `n ^ 2 * sqrt n` lower bound with constant `c * a / M`.

This statement deliberately leaves the ambient objects and profile notion
abstract.  For Problem 636, `Good` is the Ramsey condition, `spectra` is
`edgeProfilesAt`, and `profiles` is `inducedProfiles`. -/
theorem globalProfileLowerBound_of_hasBoundedMultiplicitySpectra
    {Ambient : ℕ → Type u} {E : Type v} [DecidableEq E]
    {Good : (n : ℕ) → Ambient n → Prop}
    {spectra : (n : ℕ) → Ambient n → ℕ → Finset E}
    {profiles : (n : ℕ) → Ambient n → Finset (ℕ × E)}
    (hbounded : HasBoundedMultiplicitySpectra Good spectra)
    (hcontain : ∀ n (G : Ambient n) (I : Finset ℕ),
      ProfileReduction.taggedSpectra I (spectra n G) ⊆ profiles n G) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ G : Ambient n, Good n G →
      γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ ((profiles n G).card : ℝ) := by
  rcases hbounded with ⟨c, a, hc, ha, M, hM, N, hN⟩
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  refine ⟨c * a / M, div_pos (mul_pos hc ha) hMreal, N, ?_⟩
  intro n hn G hG
  rcases hN n hn G hG with ⟨D⟩
  exact D.globalProfiles_bound (profiles n G) ha.le
    (hcontain n G (D.parameter.image D.order))

end Erdos636.OuterAssembly
