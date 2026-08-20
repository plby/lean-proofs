/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos722.Rotations
import ErdosProblems.Erdos722.ColoredTypicality
import ErdosProblems.Erdos722.Asymptotics
import ErdosProblems.Erdos722.BinomialBounds
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Scalar realization of the sparse modular-generator host

This file instantiates the two-cap greedy-and-prune package in a typical
Bernoulli `r`-graph of density `n⁻¹ᵈᵈ`.  Decimal constants from the
short proof are represented with denominator `10*d`, so all statements
remain exact natural-number inequalities.
-/

namespace Erdos722.GeneratorAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.IntegralGenerators
open Erdos722.Rotations
open Erdos722.ColoredTypicality

noncomputable section

/-- Tag every uncoloured root face with the unique colour in `Fin 1`. -/
def monochromeRootEmbedding (n : ℕ) :
    Finset (Fin n) ↪ ColoredRoot 1 n where
  toFun f := (0, f)
  inj' := by
    intro f g h
    exact congrArg Prod.snd h

def monochromeRootFamily (n : ℕ)
    (roots : Finset (Finset (Fin n))) :
    Finset (ColoredRoot 1 n) :=
  roots.map (monochromeRootEmbedding n)

lemma monochromeRootFamily_mem
    {n r h : ℕ} {roots : Finset (Finset (Fin n))}
    (hroots : roots ∈ rootFamilies n r h) :
    monochromeRootFamily n roots ∈ coloredRootFamilies 1 n r h := by
  rw [mem_coloredRootFamilies]
  constructor
  · intro z hz
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hz
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      (mem_rootFamilies.mp hroots).1 hf⟩
  · simpa [monochromeRootFamily] using (mem_rootFamilies.mp hroots).2

lemma card_rootFamilies_le_card_coloredRootFamilies_one
    (n r h : ℕ) :
    (rootFamilies n r h).card ≤ (coloredRootFamilies 1 n r h).card := by
  classical
  apply Finset.card_le_card_of_injOn (monochromeRootFamily n)
  · intro roots hroots
    exact monochromeRootFamily_mem hroots
  · intro roots hroots other hother heq
    exact Finset.map_injective (monochromeRootEmbedding n) heq

/-- The generic one-colour scalar union bound, obtained from the stronger
coloured estimate already used by the embedding layer. -/
theorem eventually_uncolored_scalar_bound
    (r h d : ℕ) (hd : 0 < d) (hhd : h < d) :
    ∀ᶠ n : ℕ in atTop,
      ((rootFamilies n r h).card : ℝ) * 2 *
          Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
            reserveProbability n d ^ h) / 10) < 1 := by
  filter_upwards [eventually_colored_scalar_bound 1 r h d hd hhd] with n hn
  have hcardNat := card_rootFamilies_le_card_coloredRootFamilies_one n r h
  have hcard : ((rootFamilies n r h).card : ℝ) ≤
      (coloredRootFamilies 1 n r h).card := by
    exact_mod_cast hcardNat
  calc
    ((rootFamilies n r h).card : ℝ) * 2 *
        Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
          reserveProbability n d ^ h) / 10) ≤
      ((coloredRootFamilies 1 n r h).card : ℝ) * 2 *
        Real.exp (-(((n - h * (r - 1) : ℕ) : ℝ) *
          reserveProbability n d ^ h) / 10) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard (by norm_num))
        (Real.exp_nonneg _)
    _ < 1 := hn

/-- For every fixed root bound below the density denominator, one
deterministic Bernoulli sample is simultaneously typical at all roots. -/
theorem eventually_exists_uncolored_typical_sample
    (r h d : ℕ) (hr : 0 < r) (hd : 0 < d) (hhd : h < d) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 0 < n,
      ∃ ω : {e // e ∈ uniformEdges n r} → Bool,
        ∀ roots, ∀ hroots : roots ∈ rootFamilies n r h,
          commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
            Erdos722.Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots hr
                (root_card_of_mem_rootFamilies hroots) x) ω ∧
          Erdos722.Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots hr
                (root_card_of_mem_rootFamilies hroots) x) ω <
            2 * commonMean n roots (reserveProbabilityIcc n d hn) := by
  filter_upwards [eventually_uncolored_scalar_bound r h d hd hhd,
    eventually_ge_atTop 1] with n hscalar hn
  have hnpos : 0 < n := by omega
  let p := reserveProbabilityIcc n d hnpos
  have htail :
      ∑ roots ∈ rootFamilies n r h,
        (Real.exp (-(commonMean n roots p) / 10) +
          Real.exp (-(commonMean n roots p) / 5)) < 1 := by
    apply Erdos722.Reserve.tail_sum_lt_one_of_scalar_bound
    simpa [p, reserveProbabilityIcc] using hscalar
  obtain ⟨ω, htyp⟩ := exists_simultaneously_typical n r h hr p htail
  exact ⟨hnpos, ω, by simpa [p] using htyp⟩

/-- A ceiling-form upper branching factor is bounded by four times its
exact rational power. -/
lemma typicalUpperBranching_cast_le_four_rpow
    {n r d i : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hi : Nat.choose (r + i) (r - 1) < d) :
    (typicalUpperBranching n r (reserveProbabilityIcc n d hn) i : ℝ) ≤
      4 * (n : ℝ) ^
        (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) := by
  let h := Nat.choose (r + i) (r - 1)
  let y := (n : ℝ) ^ (((d - h : ℕ) : ℝ) / d)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hExp : (0 : ℝ) ≤ ((d - h : ℕ) : ℝ) / d := by positivity
  have hyOne : (1 : ℝ) ≤ y := Real.one_le_rpow hnOne hExp
  have hp : (reserveProbability n d) ^ h =
      (n : ℝ) ^ (-((h : ℝ) / (d : ℝ))) :=
    reserveProbability_pow_nat hn hd h
  have hexp :
      (1 : ℝ) - (h : ℝ) / d = ((d - h : ℕ) : ℝ) / d := by
    rw [Nat.cast_sub (by omega : h ≤ d)]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  have hny : (n : ℝ) *
      (reserveProbabilityIcc n d hn : ℝ) ^ h = y := by
    change (n : ℝ) * reserveProbability n d ^ h = y
    rw [hp]
    calc
      (n : ℝ) * (n : ℝ) ^ (-((h : ℝ) / d)) =
          (n : ℝ) ^ (1 : ℝ) *
            (n : ℝ) ^ (-((h : ℝ) / d)) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) - (h : ℝ) / d) := by
        rw [← Real.rpow_add hnR]
        congr 2
      _ = y := by rw [hexp]
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 2 * (n : ℝ) *
      (reserveProbabilityIcc n d hn : ℝ) ^ h by
        exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
          (pow_nonneg (reserveProbabilityIcc n d hn).property.1 h))
  change (typicalUpperBranching n r
      (reserveProbabilityIcc n d hn) i : ℝ) <
    2 * (n : ℝ) * (reserveProbabilityIcc n d hn : ℝ) ^ h + 1 at hceil
  change (typicalUpperBranching n r
      (reserveProbabilityIcc n d hn) i : ℝ) ≤ 4 * y
  rw [show 2 * (n : ℝ) *
      (reserveProbabilityIcc n d hn : ℝ) ^ h = 2 * y by rw [← hny]; ring]
    at hceil
  linarith

lemma extensionRootCount_lt_den
    {q r d i : ℕ} (hr : 0 < r) (hrq : r < q)
    (hi : i < q - r) (hqd : Nat.choose q r < d) :
    Nat.choose (r + i) (r - 1) < d := by
  have himem : i ∈ Finset.range (q - r) := Finset.mem_range.mpr hi
  have hle : Nat.choose (r + i) (r - 1) ≤
      ∑ j ∈ Finset.range (q - r), Nat.choose (r + j) (r - 1) := by
    exact Finset.single_le_sum
      (f := fun j ↦ Nat.choose (r + j) (r - 1))
      (fun _ _ ↦ Nat.zero_le _) himem
  rw [Erdos722.Reserve.sum_extension_root_counts r (q - r) hr,
    Nat.add_sub_of_le hrq.le] at hle
  omega

lemma prod_rpow_eq_rpow_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) {x : ℝ} (hx : 0 < x) :
    ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.mem_insert, Finset.prod_insert ha, Finset.sum_insert ha]
      rw [ih, Real.rpow_add hx]

/-- The lower-face saturation cap `n^(1-0.7/d)`. -/
def generatorFaceCap (d n : ℕ) : ℕ :=
  rationalPowerThreshold (10 * d - 7) (10 * d) n

/-- The independent edge-multiplicity cap `n^(0.001/d)`.

The much smaller exponent is the quantitative separation between Keevash's
face-density parameter and the multiplicity parameter used by the later
fourth-power flattening estimate. -/
def generatorEdgeCap (d n : ℕ) : ℕ :=
  rationalPowerThreshold 1 (1000 * d) n

/-- A fixed safety divisor making the exceptional-clique threshold a
small constant fraction of the typical clique count. -/
def generatorPruneDivisor (q r : ℕ) : ℕ :=
  8 * 16 ^ (q - r) * (2 ^ q) ^ (q - r)

/-- An edge is deleted after it lies in this many exceptional cliques. -/
def generatorPruneThreshold (q r d n : ℕ) : ℕ :=
  rationalPowerThreshold
      (d * (q - r) - (Nat.choose q r - 1)) d n /
    generatorPruneDivisor q r

/-- Integer upper branching factors supplied by typicality. -/
def generatorUpperBranching (d n r i : ℕ) : ℕ :=
  if hn : 0 < n then
    typicalUpperBranching n r (reserveProbabilityIcc n d hn) i
  else 0

/-- Product upper bound for cliques through one host edge. -/
def generatorEdgeCliqueCap (q r d n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range (q - r), generatorUpperBranching d n r i

/-- Product upper bound for cliques through one lower face. -/
def generatorFaceCliqueCap (q r d n : ℕ) : ℕ :=
  (if hn : 0 < n then
      typicalFaceDegreeCap n (reserveProbabilityIcc n d hn)
    else 0) * generatorEdgeCliqueCap q r d n

/-- A deliberately quartered lower branching factor.  The factor four
pays for the clean-vertex loss and the strict lower-half typicality bound. -/
def generatorLowerBranching (d n r i : ℕ) : ℕ :=
  rationalPowerThreshold
    (d - Nat.choose (r + i) (r - 1)) d n / 4

/-- The extension-tree lower count after its bounded labelling
multiplicity is removed. -/
def generatorCliqueLower (q r d n : ℕ) : ℕ :=
  (∏ i ∈ Finset.range (q - r),
      generatorLowerBranching d n r i) /
    (2 ^ q) ^ (q - r)

/-- A quartered one-face degree lower threshold. -/
def generatorDegreeLower (d n : ℕ) : ℕ :=
  rationalPowerThreshold (d - 1) d n / 4

/-- A natural quotient loses at most another factor two once its real
input is at least twice the denominator. -/
lemma half_div_le_natDiv (x C : ℕ) (hC : 0 < C)
    (hx : 2 * C ≤ x) :
    (x : ℝ) / (2 * C) ≤ (x / C : ℕ) := by
  have hy : 2 ≤ x / C :=
    (Nat.le_div_iff_mul_le hC).2 (by simpa [Nat.mul_comm] using hx)
  have hrem : x % C ≤ C * (x / C) := by
    exact (Nat.le_of_lt (Nat.mod_lt x hC)).trans
      (Nat.le_mul_of_pos_right C (by omega : 0 < x / C))
  have hdecomp := Nat.div_add_mod x C
  have hle : x ≤ (x / C) * (2 * C) := by
    calc
      x = C * (x / C) + x % C := hdecomp.symm
      _ ≤ C * (x / C) + C * (x / C) := Nat.add_le_add_left hrem _
      _ = (x / C) * (2 * C) := by ring
  rw [div_le_iff₀ (by positivity)]
  exact_mod_cast hle

lemma generatorPruneDivisor_pos (q r : ℕ) :
    0 < generatorPruneDivisor q r := by
  simp [generatorPruneDivisor]

/-- Lower asymptotic estimate for the small exceptional-clique threshold. -/
lemma eventually_generatorPruneThreshold_lower
    {q r d : ℕ}
    (hnum : 0 < d * (q - r) - (Nat.choose q r - 1)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
            (4 * generatorPruneDivisor q r) ≤
        (generatorPruneThreshold q r d n : ℝ) := by
  let P := generatorPruneDivisor q r
  have hP : 0 < P := generatorPruneDivisor_pos q r
  have hhalf := eventually_half_rpow_le_rationalPowerThreshold hnum hd
  have hlarge :=
    (rationalPowerThreshold_tendsto_atTop hnum hd).eventually
      (eventually_ge_atTop (2 * P))
  filter_upwards [hhalf, hlarge] with n hhalf hlarge
  have hdiv := half_div_le_natDiv
    (rationalPowerThreshold
      (d * (q - r) - (Nat.choose q r - 1)) d n) P hP hlarge
  have hresult :
      (n : ℝ) ^
            (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
          (4 * P) ≤
        (rationalPowerThreshold
          (d * (q - r) - (Nat.choose q r - 1)) d n / P : ℕ) := by
    calc
      (n : ℝ) ^
            (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
          (4 * P) ≤
        (rationalPowerThreshold
          (d * (q - r) - (Nat.choose q r - 1)) d n : ℝ) /
            (2 * P) := by
              have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
              calc
                (n : ℝ) ^
                      (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
                    (4 * P) =
                  ((n : ℝ) ^
                      (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
                    2) / (2 * P) := by ring
                _ ≤ (rationalPowerThreshold
                    (d * (q - r) - (Nat.choose q r - 1)) d n : ℝ) /
                      (2 * P) :=
                  (div_le_div_iff_of_pos_right (by positivity :
                    (0 : ℝ) < 2 * P)).2 hhalf
      _ ≤ _ := hdiv
  simpa [generatorPruneThreshold, P] using hresult

@[simp] lemma generatorUpperBranching_eq
    (d r i : ℕ) {n : ℕ} (hn : 0 < n) :
    generatorUpperBranching d n r i =
      typicalUpperBranching n r (reserveProbabilityIcc n d hn) i := by
  simp [generatorUpperBranching, hn]

@[simp] lemma generatorFaceCliqueCap_eq
    (q r d : ℕ) {n : ℕ} (hn : 0 < n) :
    generatorFaceCliqueCap q r d n =
      typicalFaceDegreeCap n (reserveProbabilityIcc n d hn) *
        ∏ i ∈ Finset.range (q - r),
          typicalUpperBranching n r (reserveProbabilityIcc n d hn) i := by
  simp [generatorFaceCliqueCap, generatorEdgeCliqueCap, hn]

@[simp] lemma generatorEdgeCliqueCap_eq
    (q r d : ℕ) {n : ℕ} (hn : 0 < n) :
    generatorEdgeCliqueCap q r d n =
      ∏ i ∈ Finset.range (q - r),
        typicalUpperBranching n r (reserveProbabilityIcc n d hn) i := by
  simp [generatorEdgeCliqueCap, hn]

/-- Product upper estimate for all extension levels through one edge. -/
lemma generatorEdgeCliqueCap_cast_le
    {n q r d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hr : 0 < r) (hrq : r < q) (hqd : Nat.choose q r < d) :
    (generatorEdgeCliqueCap q r d n : ℝ) ≤
      (4 : ℝ) ^ (q - r) * (n : ℝ) ^
        (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) := by
  rw [generatorEdgeCliqueCap_eq q r d hn]
  push_cast
  calc
    ∏ i ∈ Finset.range (q - r),
        (typicalUpperBranching n r (reserveProbabilityIcc n d hn) i : ℝ) ≤
      ∏ i ∈ Finset.range (q - r),
        (4 * (n : ℝ) ^
          (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact typicalUpperBranching_cast_le_four_rpow hn hd
          (extensionRootCount_lt_den hr hrq (Finset.mem_range.mp hi) hqd)
    _ = (4 : ℝ) ^ (q - r) *
        ∏ i ∈ Finset.range (q - r),
          (n : ℝ) ^
            (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ = (4 : ℝ) ^ (q - r) * (n : ℝ) ^
        (∑ i ∈ Finset.range (q - r),
          (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d)) := by
      rw [prod_rpow_eq_rpow_sum _ _ (by exact_mod_cast hn)]
    _ = (4 : ℝ) ^ (q - r) * (n : ℝ) ^
        (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) := by
      congr 2
      have hrootLe : ∀ i ∈ Finset.range (q - r),
          Nat.choose (r + i) (r - 1) ≤ d := by
        intro i hi
        exact (extensionRootCount_lt_den hr hrq
          (Finset.mem_range.mp hi) hqd).le
      have hsum : ∑ i ∈ Finset.range (q - r),
          Nat.choose (r + i) (r - 1) = Nat.choose q r - 1 := by
        simpa [Nat.add_sub_of_le hrq.le] using
          Erdos722.Reserve.sum_extension_root_counts r (q - r) hr
      have hsub : Nat.choose q r - 1 ≤ d * (q - r) := by
        rw [← hsum]
        calc
          ∑ i ∈ Finset.range (q - r), Nat.choose (r + i) (r - 1) ≤
              ∑ _i ∈ Finset.range (q - r), d := by
            exact Finset.sum_le_sum hrootLe
          _ = d * (q - r) := by simp [Nat.mul_comm]
      calc
        ∑ i ∈ Finset.range (q - r),
            (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) =
          ∑ i ∈ Finset.range (q - r),
            (((d : ℝ) - Nat.choose (r + i) (r - 1)) / d) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Nat.cast_sub (hrootLe i hi)]
        _ = (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) := by
          rw [Nat.cast_sub hsub]
          push_cast
          rw [← hsum]
          rw [← Finset.sum_div, Finset.sum_sub_distrib]
          simp
          ring

lemma typicalFaceDegreeCap_cast_le_four_rpow
    {n d : ℕ} (hn : 0 < n) (hd : 1 < d) :
    (typicalFaceDegreeCap n (reserveProbabilityIcc n d hn) : ℝ) ≤
      4 * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) := by
  simpa [typicalUpperBranching, typicalFaceDegreeCap] using
    (typicalUpperBranching_cast_le_four_rpow
      (r := 1) (i := 0) hn (by omega : 0 < d) (by simpa using hd))

/-- Product upper estimate for the cliques through one lower face. -/
lemma generatorFaceCliqueCap_cast_le
    {n q r d : ℕ} (hn : 0 < n) (hd : 1 < d)
    (hr : 0 < r) (hrq : r < q) (hqd : Nat.choose q r < d) :
    (generatorFaceCliqueCap q r d n : ℝ) ≤
      (4 : ℝ) ^ (q - r + 1) * (n : ℝ) ^
        (((d * (q - r + 1) - Nat.choose q r : ℕ) : ℝ) / d) := by
  rw [generatorFaceCliqueCap_eq q r d hn]
  push_cast
  have hface := typicalFaceDegreeCap_cast_le_four_rpow hn hd
  have hedge := generatorEdgeCliqueCap_cast_le hn (by omega : 0 < d)
    hr hrq hqd
  rw [generatorEdgeCliqueCap_eq q r d hn] at hedge
  push_cast at hedge
  have hm : 1 ≤ q - r := by omega
  have hsubEdge : Nat.choose q r - 1 ≤ d * (q - r) := by
    calc
      Nat.choose q r - 1 ≤ d := by omega
      _ ≤ d * (q - r) := Nat.le_mul_of_pos_right d (by omega)
  have hsubFace : Nat.choose q r ≤ d * (q - r + 1) := by
    have : Nat.choose q r ≤ d := by omega
    exact this.trans (Nat.le_mul_of_pos_right d (by omega))
  calc
    (typicalFaceDegreeCap n (reserveProbabilityIcc n d hn) : ℝ) *
        (∏ i ∈ range (q - r),
          (typicalUpperBranching n r
            (reserveProbabilityIcc n d hn) i : ℝ)) ≤
      (4 * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d)) *
        ((4 : ℝ) ^ (q - r) * (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d)) := by
      exact mul_le_mul hface hedge (by positivity) (by positivity)
    _ = (4 : ℝ) ^ (q - r + 1) * (n : ℝ) ^
        (((d * (q - r + 1) - Nat.choose q r : ℕ) : ℝ) / d) := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      calc
        (4 * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d)) *
            ((4 : ℝ) ^ (q - r) * (n : ℝ) ^
              (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d)) =
          (4 * (4 : ℝ) ^ (q - r)) *
            ((n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) *
              (n : ℝ) ^
                (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d)) := by
                  ring
        _ = (4 : ℝ) ^ (q - r + 1) * (n : ℝ) ^
            ((((d - 1 : ℕ) : ℝ) / d) +
              (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d)) := by
          rw [← Real.rpow_add hnR]
          congr 1
          ring
        _ = (4 : ℝ) ^ (q - r + 1) * (n : ℝ) ^
            (((d * (q - r + 1) - Nat.choose q r : ℕ) : ℝ) / d) := by
          congr 2
          rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_sub hsubEdge,
            Nat.cast_sub hsubFace,
            Nat.cast_sub (by
              have := Nat.choose_pos hrq.le
              omega : 1 ≤ Nat.choose q r)]
          push_cast
          field_simp
          ring

/-- The polynomial gap of `1/(10*d)` makes the division-free pruning
loss smaller than half of the sampled host. -/
theorem eventually_generator_pruning_scalar
    (N q r d : ℕ) (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      2 * N *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
              generatorFaceCliqueCap q r d n +
            Nat.choose q r * generatorFaceCap d n *
              generatorEdgeCliqueCap q r d n) * Nat.choose q r ≤
        generatorFaceCap d n * generatorEdgeCap d n *
          generatorPruneThreshold q r d n := by
  let m := q - r
  let K := Nat.choose q r
  let faceExp : ℝ := ((10 * d - 7 : ℕ) : ℝ) / (10 * d)
  let edgeExp : ℝ := (1 : ℝ) / (1000 * d)
  let pruneExp : ℝ := ((d * m - (K - 1) : ℕ) : ℝ) / d
  let edgeCliqueExp : ℝ := ((d * m - (K - 1) : ℕ) : ℝ) / d
  let faceCliqueExp : ℝ := ((d * (m + 1) - K : ℕ) : ℝ) / d
  let rhsExp := faceExp + edgeExp + pruneExp
  let termFaceExp := edgeExp + faceCliqueExp
  let termEdgeExp := faceExp + edgeCliqueExp
  let P := generatorPruneDivisor q r
  let Cface : ℝ :=
    2 * N * K * Nat.choose q (r - 1) * (4 : ℝ) ^ (m + 1)
  let Cedge : ℝ :=
    2 * N * K * K * (4 : ℝ) ^ m
  have hKpos : 0 < K := by
    dsimp [K]
    exact Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hdOne : 1 < d := by omega
  have hm : 0 < m := by dsimp [m]; omega
  have hfaceSub : 7 ≤ 10 * d := by nlinarith
  have hedgeSub : K - 1 ≤ d * m := by
    have hd_le : d ≤ d * m := Nat.le_mul_of_pos_right d hm
    omega
  have hprunePos : 0 < d * m - (K - 1) := by
    apply Nat.sub_pos_of_lt
    exact (by omega : K - 1 < d).trans_le
      (Nat.le_mul_of_pos_right d hm)
  have hfaceCliqueSub : K ≤ d * (m + 1) := by
    have hd_le : d ≤ d * (m + 1) :=
      Nat.le_mul_of_pos_right d (by omega)
    omega
  have htermFace : termFaceExp < rhsExp := by
    dsimp [termFaceExp, rhsExp, faceExp, edgeExp, pruneExp,
      faceCliqueExp, m, K]
    rw [Nat.cast_sub hfaceSub, Nat.cast_sub hedgeSub,
      Nat.cast_sub hfaceCliqueSub,
      Nat.cast_sub (by omega : 1 ≤ Nat.choose q r)]
    push_cast
    field_simp
    nlinarith
  have htermEdge : termEdgeExp < rhsExp := by
    dsimp [termEdgeExp, rhsExp, faceExp, edgeExp, pruneExp,
      edgeCliqueExp, m, K]
    rw [Nat.cast_sub hfaceSub, Nat.cast_sub hedgeSub,
      Nat.cast_sub (by omega : 1 ≤ Nat.choose q r)]
    push_cast
    field_simp
    nlinarith
  have hP : 0 < P := generatorPruneDivisor_pos q r
  have hCface : 0 ≤ (32 : ℝ) * P * Cface := by positivity
  have hCedge : 0 ≤ (32 : ℝ) * P * Cedge := by positivity
  have hsmallFace := eventually_const_mul_rpow_le_rpow htermFace hCface
  have hsmallEdge := eventually_const_mul_rpow_le_rpow htermEdge hCedge
  have hfaceLower := eventually_half_rpow_le_rationalPowerThreshold
    (E := 10 * d - 7) (d := 10 * d) (by omega) (by positivity)
  have hedgeLower := eventually_half_rpow_le_rationalPowerThreshold
    (E := 1) (d := 1000 * d) (by omega) (by positivity)
  have hpruneLower := eventually_generatorPruneThreshold_lower
    (q := q) (r := r) (d := d)
      (by simpa [m, K] using hprunePos) hd
  filter_upwards [hsmallFace, hsmallEdge, hfaceLower, hedgeLower,
    hpruneLower, eventually_ge_atTop 1] with n hsmallFace hsmallEdge
      hfaceLower hedgeLower hpruneLower hn
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfaceUpper : (generatorFaceCap d n : ℝ) ≤
      (n : ℝ) ^ faceExp := by
    simpa [generatorFaceCap, faceExp] using
      rationalPowerThreshold_cast_le (10 * d - 7) (10 * d) n
  have hedgeUpper : (generatorEdgeCap d n : ℝ) ≤
      (n : ℝ) ^ edgeExp := by
    simpa [generatorEdgeCap, edgeExp] using
      rationalPowerThreshold_cast_le 1 (1000 * d) n
  have hMedge : (generatorEdgeCliqueCap q r d n : ℝ) ≤
      (4 : ℝ) ^ m * (n : ℝ) ^ edgeCliqueExp := by
    simpa [m, K, edgeCliqueExp] using
      generatorEdgeCliqueCap_cast_le hnpos hd hr hrq hqd
  have hMface : (generatorFaceCliqueCap q r d n : ℝ) ≤
      (4 : ℝ) ^ (m + 1) * (n : ℝ) ^ faceCliqueExp := by
    simpa [m, K, faceCliqueExp] using
      generatorFaceCliqueCap_cast_le hnpos hdOne hr hrq hqd
  have htermFaceUpper :
      ((2 * N * K * (Nat.choose q (r - 1) * generatorEdgeCap d n *
          generatorFaceCliqueCap q r d n) : ℕ) : ℝ) ≤
        Cface * (n : ℝ) ^ termFaceExp := by
    push_cast
    calc
      2 * (N : ℝ) * K *
          ((Nat.choose q (r - 1) : ℝ) * generatorEdgeCap d n *
            generatorFaceCliqueCap q r d n) ≤
        2 * (N : ℝ) * K *
          ((Nat.choose q (r - 1) : ℝ) * (n : ℝ) ^ edgeExp *
            ((4 : ℝ) ^ (m + 1) * (n : ℝ) ^ faceCliqueExp)) := by
          gcongr
      _ = Cface * (n : ℝ) ^ termFaceExp := by
        calc
          2 * (N : ℝ) * K *
              ((Nat.choose q (r - 1) : ℝ) * (n : ℝ) ^ edgeExp *
                ((4 : ℝ) ^ (m + 1) * (n : ℝ) ^ faceCliqueExp)) =
            Cface * ((n : ℝ) ^ edgeExp *
              (n : ℝ) ^ faceCliqueExp) := by
                dsimp [Cface]
                ring
          _ = Cface * (n : ℝ) ^ termFaceExp := by
            dsimp [termFaceExp]
            rw [← Real.rpow_add hnR]
  have htermEdgeUpper :
      ((2 * N * K * (K * generatorFaceCap d n *
          generatorEdgeCliqueCap q r d n) : ℕ) : ℝ) ≤
        Cedge * (n : ℝ) ^ termEdgeExp := by
    push_cast
    calc
      2 * (N : ℝ) * K *
          ((K : ℝ) * generatorFaceCap d n *
            generatorEdgeCliqueCap q r d n) ≤
        2 * (N : ℝ) * K *
          ((K : ℝ) * (n : ℝ) ^ faceExp *
            ((4 : ℝ) ^ m * (n : ℝ) ^ edgeCliqueExp)) := by
          gcongr
      _ = Cedge * (n : ℝ) ^ termEdgeExp := by
        calc
          2 * (N : ℝ) * K *
              ((K : ℝ) * (n : ℝ) ^ faceExp *
                ((4 : ℝ) ^ m * (n : ℝ) ^ edgeCliqueExp)) =
            Cedge * ((n : ℝ) ^ faceExp *
              (n : ℝ) ^ edgeCliqueExp) := by
                dsimp [Cedge]
                ring
          _ = Cedge * (n : ℝ) ^ termEdgeExp := by
            dsimp [termEdgeExp]
            rw [← Real.rpow_add hnR]
  have hsmallFace' : Cface * (n : ℝ) ^ termFaceExp ≤
      (n : ℝ) ^ rhsExp / (32 * P) := by
    have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * P)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsmallFace
  have hsmallEdge' : Cedge * (n : ℝ) ^ termEdgeExp ≤
      (n : ℝ) ^ rhsExp / (32 * P) := by
    have hPReal : (0 : ℝ) < P := by exact_mod_cast hP
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 32 * P)).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsmallEdge
  have hleft :
      ((2 * N *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
              generatorFaceCliqueCap q r d n +
            Nat.choose q r * generatorFaceCap d n *
              generatorEdgeCliqueCap q r d n) * Nat.choose q r : ℕ) : ℝ) ≤
        (n : ℝ) ^ rhsExp / (16 * P) := by
    have hsum := add_le_add
      (htermFaceUpper.trans hsmallFace')
      (htermEdgeUpper.trans hsmallEdge')
    calc
      ((2 * N *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
              generatorFaceCliqueCap q r d n +
            Nat.choose q r * generatorFaceCap d n *
              generatorEdgeCliqueCap q r d n) * Nat.choose q r : ℕ) : ℝ) =
        ((2 * N * K *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
            generatorFaceCliqueCap q r d n) : ℕ) : ℝ) +
        ((2 * N * K *
          (K * generatorFaceCap d n *
            generatorEdgeCliqueCap q r d n) : ℕ) : ℝ) := by
              push_cast
              dsimp [K]
              ring
      _ ≤ (n : ℝ) ^ rhsExp / (32 * P) +
          (n : ℝ) ^ rhsExp / (32 * P) := hsum
      _ = (n : ℝ) ^ rhsExp / (16 * P) := by ring
  have hfaceLower' : (n : ℝ) ^ faceExp / 2 ≤
      generatorFaceCap d n := by simpa [generatorFaceCap, faceExp] using hfaceLower
  have hedgeLower' : (n : ℝ) ^ edgeExp / 2 ≤
      generatorEdgeCap d n := by simpa [generatorEdgeCap, edgeExp] using hedgeLower
  have hpruneLower' : (n : ℝ) ^ pruneExp / (4 * P) ≤
      generatorPruneThreshold q r d n := by
    simpa [pruneExp, m, K, P] using hpruneLower
  have hright : (n : ℝ) ^ rhsExp / (16 * P) ≤
      ((generatorFaceCap d n * generatorEdgeCap d n *
        generatorPruneThreshold q r d n : ℕ) : ℝ) := by
    push_cast
    calc
      (n : ℝ) ^ rhsExp / (16 * P) =
          ((n : ℝ) ^ faceExp / 2) * ((n : ℝ) ^ edgeExp / 2) *
            ((n : ℝ) ^ pruneExp / (4 * P)) := by
        have hrpow : (n : ℝ) ^ rhsExp =
            (n : ℝ) ^ faceExp * (n : ℝ) ^ edgeExp *
              (n : ℝ) ^ pruneExp := by
          dsimp [rhsExp]
          rw [Real.rpow_add hnR, Real.rpow_add hnR]
        rw [hrpow]
        ring
      _ ≤ (generatorFaceCap d n : ℝ) * generatorEdgeCap d n *
          generatorPruneThreshold q r d n := by
        gcongr
  exact_mod_cast hleft.trans hright

/-- A simultaneous typical sample feeds directly into the exact finite
two-cap greedy-and-prune package. -/
theorem exists_generatorTwoCapPrunedData
    {N n q r d : ℕ} (hN : 0 < N) (hn : 0 < n)
    (hr : 1 < r) (hrq : r < q)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn)) :
    ∃ D : TwoCapPrunedData N n q r
        (generatorFaceCap d n) (generatorEdgeCap d n)
        (generatorPruneThreshold q r d n)
        (generatorFaceCliqueCap q r d n)
        (generatorEdgeCliqueCap q r d n),
      D.K = sampledEdges n r ω := by
  apply exists_twoCapPrunedData hN (sampledEdges n r ω)
  · intro e he
    exact mem_uniformEdges.mp (sampledEdges_subset ω he)
  · intro f hf
    have h := card_cliques_through_face_typicalUpper_le
      hr hrq (reserveProbabilityIcc n d hn) ω htyp
      (mem_uniformEdges.mp hf)
    rw [generatorFaceCliqueCap_eq q r d hn]
    exact h
  · intro e he
    have h := card_cliques_through_edge_typicalUpper_le
      hr hrq (reserveProbabilityIcc n d hn) ω htyp
      (mem_uniformEdges.mp he)
    rw [generatorEdgeCliqueCap_eq q r d hn]
    exact h

lemma generatorFaceCap_pos_eventually (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, 0 < generatorFaceCap d n := by
  have hnum : 0 < 10 * d - 7 := by omega
  have hden : 0 < 10 * d := by positivity
  have ht := rationalPowerThreshold_tendsto_atTop hnum hden
  exact ht.eventually (eventually_gt_atTop 0)

lemma generatorEdgeCap_pos_eventually (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, 0 < generatorEdgeCap d n := by
  have hden : 0 < 1000 * d := by positivity
  have ht := rationalPowerThreshold_tendsto_atTop (by omega : 0 < 1) hden
  exact ht.eventually (eventually_gt_atTop 0)

lemma generatorPruneThreshold_pos_eventually
    (hrq : r < q) (hchoose : Nat.choose q r - 1 < d * (q - r))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, 0 < generatorPruneThreshold q r d n := by
  have hnum : 0 < d * (q - r) - (Nat.choose q r - 1) := by omega
  have ht := rationalPowerThreshold_tendsto_atTop hnum hd
  let P := generatorPruneDivisor q r
  have hP : 0 < P := generatorPruneDivisor_pos q r
  have hlarge := ht.eventually (eventually_ge_atTop P)
  filter_upwards [hlarge] with n hn
  exact Nat.div_pos hn hP

/-- Eventual lower estimate for the quartered rational threshold. -/
lemma eventually_rpow_div_sixteen_le_threshold_div_four
    {E d : ℕ} (hE : 0 < E) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((E : ℝ) / d) / 16 ≤
        (rationalPowerThreshold E d n / 4 : ℕ) := by
  have hhalf := eventually_half_rpow_le_rationalPowerThreshold hE hd
  have hlarge :=
    (rationalPowerThreshold_tendsto_atTop hE hd).eventually
      (eventually_ge_atTop 8)
  filter_upwards [hhalf, hlarge] with n hhalf hlarge
  calc
    (n : ℝ) ^ ((E : ℝ) / d) / 16 ≤
        (rationalPowerThreshold E d n : ℝ) / 8 := by linarith
    _ ≤ (rationalPowerThreshold E d n / 4 : ℕ) := by
      convert half_div_le_natDiv _ 4 (by omega) hlarge using 1 <;> norm_num

lemma sum_extensionDeficit_exponents
    {q r d : ℕ} (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∑ i ∈ Finset.range (q - r),
        (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) =
      ((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d := by
  have hd : 0 < d := (Nat.choose_pos hrq.le).trans hqd
  have hrootLe : ∀ i ∈ Finset.range (q - r),
      Nat.choose (r + i) (r - 1) ≤ d := by
    intro i hi
    exact (extensionRootCount_lt_den hr hrq
      (Finset.mem_range.mp hi) hqd).le
  have hsum : ∑ i ∈ Finset.range (q - r),
      Nat.choose (r + i) (r - 1) = Nat.choose q r - 1 := by
    simpa [Nat.add_sub_of_le hrq.le] using
      Erdos722.Reserve.sum_extension_root_counts r (q - r) hr
  have hsub : Nat.choose q r - 1 ≤ d * (q - r) := by
    rw [← hsum]
    calc
      ∑ i ∈ Finset.range (q - r), Nat.choose (r + i) (r - 1) ≤
          ∑ _i ∈ Finset.range (q - r), d := Finset.sum_le_sum hrootLe
      _ = d * (q - r) := by simp [Nat.mul_comm]
  calc
    ∑ i ∈ Finset.range (q - r),
        (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) =
      ∑ i ∈ Finset.range (q - r),
        (((d : ℝ) - Nat.choose (r + i) (r - 1)) / d) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Nat.cast_sub (hrootLe i hi)]
    _ = ((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d := by
      rw [Nat.cast_sub hsub]
      push_cast
      rw [← hsum, ← Finset.sum_div, Finset.sum_sub_distrib]
      simp
      ring

/-- The product of the integer lower branching factors retains its full
telescoping power, with only the explicit constant `16^(q-r)` lost. -/
theorem eventually_generatorLowerBranching_prod_lower
    (q r d : ℕ) (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
            (16 : ℝ) ^ (q - r) ≤
        (∏ i ∈ Finset.range (q - r),
          generatorLowerBranching d n r i : ℕ) := by
  have hd : 0 < d := (Nat.choose_pos hrq.le).trans hqd
  have hall : ∀ᶠ n : ℕ in atTop,
      ∀ i ∈ Finset.range (q - r),
        (n : ℝ) ^
            (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) / 16 ≤
          (generatorLowerBranching d n r i : ℝ) := by
    rw [Finset.eventually_all]
    intro i hi
    have hcount := extensionRootCount_lt_den hr hrq
      (Finset.mem_range.mp hi) hqd
    simpa [generatorLowerBranching] using
      eventually_rpow_div_sixteen_le_threshold_div_four
        (E := d - Nat.choose (r + i) (r - 1)) (d := d)
        (by omega) hd
  filter_upwards [hall, eventually_ge_atTop 1] with n hall hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  push_cast
  calc
    (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
        (16 : ℝ) ^ (q - r) =
      ∏ i ∈ Finset.range (q - r),
        ((n : ℝ) ^
            (((d - Nat.choose (r + i) (r - 1) : ℕ) : ℝ) / d) / 16) := by
          rw [Finset.prod_div_distrib]
          simp only [Finset.prod_const, Finset.card_range]
          rw [prod_rpow_eq_rpow_sum _ _ hnR,
            sum_extensionDeficit_exponents hr hrq hqd]
    _ ≤ ∏ i ∈ Finset.range (q - r),
        (generatorLowerBranching d n r i : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hall i hi

/-- After removing the bounded labelling multiplicity, the natural clique
lower bound still has the expected power. -/
theorem eventually_generatorCliqueLower_lower
    (q r d : ℕ) (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
            (2 * (16 : ℝ) ^ (q - r) * (2 ^ q : ℝ) ^ (q - r)) ≤
        (generatorCliqueLower q r d n : ℝ) := by
  let C := (2 ^ q) ^ (q - r)
  let a : ℝ :=
    ((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d
  have hKpos := Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hm : 0 < q - r := by omega
  have hnum : 0 < d * (q - r) - (Nat.choose q r - 1) := by
    apply Nat.sub_pos_of_lt
    exact (by omega : Nat.choose q r - 1 < d).trans_le
      (Nat.le_mul_of_pos_right d hm)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hprod := eventually_generatorLowerBranching_prod_lower
    q r d hr hrq hqd
  have hlarge := eventually_const_mul_rpow_le_rpow
    (a := 0) (b := a)
    (C := (2 : ℝ) * C * (16 : ℝ) ^ (q - r)) ha (by positivity)
  filter_upwards [hprod, hlarge, eventually_ge_atTop 1] with n hprod hlarge hn
  let x := ∏ i ∈ Finset.range (q - r), generatorLowerBranching d n r i
  have hC : 0 < C := by simp [C]
  have hxlarge : 2 * C ≤ x := by
    have hlarge' : ((2 * C : ℕ) : ℝ) ≤
        (n : ℝ) ^ a / (16 : ℝ) ^ (q - r) := by
      rw [le_div_iff₀ (by positivity)]
      simpa [a, C] using hlarge
    have hxlargeR : ((2 * C : ℕ) : ℝ) ≤ (x : ℝ) :=
      hlarge'.trans (by simpa [a, x] using hprod)
    exact_mod_cast hxlargeR
  have hdiv := half_div_le_natDiv x C hC hxlarge
  have hresult :
      (n : ℝ) ^ a /
            (2 * (16 : ℝ) ^ (q - r) * (C : ℝ)) ≤
          (x / C : ℕ) := by
    calc
      (n : ℝ) ^ a /
            (2 * (16 : ℝ) ^ (q - r) * (C : ℝ)) =
          ((n : ℝ) ^ a / (16 : ℝ) ^ (q - r)) / (2 * C) := by ring
      _ ≤ (x : ℝ) / (2 * C) := by
        exact div_le_div_of_nonneg_right
          (by simpa [a, x] using hprod) (by positivity)
      _ ≤ (x / C : ℕ) := hdiv
  simpa [generatorCliqueLower, x, C, a] using hresult

/-- The exceptional threshold is at most half of the guaranteed clique
count; this is the quantitative input needed by `good_lower`. -/
theorem eventually_two_mul_generatorPruneThreshold_le_cliqueLower
    (q r d : ℕ) (hr : 0 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      2 * generatorPruneThreshold q r d n ≤
        generatorCliqueLower q r d n := by
  let A : ℝ := (16 : ℝ) ^ (q - r) * (2 ^ q : ℝ) ^ (q - r)
  let a : ℝ :=
    ((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d
  have hdivisor : (generatorPruneDivisor q r : ℝ) = 8 * A := by
    dsimp [A]
    simp [generatorPruneDivisor]
    ring
  have hlower := eventually_generatorCliqueLower_lower q r d hr hrq hqd
  filter_upwards [hlower, eventually_ge_atTop 1] with n hlower hn
  have hthreshold : (generatorPruneThreshold q r d n : ℝ) ≤
      (n : ℝ) ^ a / (8 * A) := by
    calc
      (generatorPruneThreshold q r d n : ℝ) ≤
          (rationalPowerThreshold
            (d * (q - r) - (Nat.choose q r - 1)) d n : ℝ) /
              generatorPruneDivisor q r := by
        simpa [generatorPruneThreshold] using
          (Nat.cast_div_le :
            ((rationalPowerThreshold
              (d * (q - r) - (Nat.choose q r - 1)) d n /
                generatorPruneDivisor q r : ℕ) : ℝ) ≤
              (rationalPowerThreshold
                (d * (q - r) - (Nat.choose q r - 1)) d n : ℝ) /
                  generatorPruneDivisor q r)
      _ ≤ (n : ℝ) ^ a / generatorPruneDivisor q r := by
        exact div_le_div_of_nonneg_right
          (by simpa [a] using
            (rationalPowerThreshold_cast_le
              (d * (q - r) - (Nat.choose q r - 1)) d n))
          (by positivity)
      _ = (n : ℝ) ^ a / (8 * A) := by
        rw [hdivisor]
  have hreal : ((2 * generatorPruneThreshold q r d n : ℕ) : ℝ) ≤
      (generatorCliqueLower q r d n : ℝ) := by
    push_cast
    calc
      2 * (generatorPruneThreshold q r d n : ℝ) ≤
          2 * ((n : ℝ) ^ a / (8 * A)) := by gcongr
      _ ≤ (n : ℝ) ^ a / (2 * A) := by
        have hA : 0 < A := by positivity
        rw [show 2 * ((n : ℝ) ^ a / (8 * A)) =
          (n : ℝ) ^ a / (4 * A) by ring]
        exact (div_le_div_iff_of_pos_left
          (Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < n)) a)
          (by positivity) (by positivity)).2 (by nlinarith)
      _ ≤ (generatorCliqueLower q r d n : ℝ) := by
        simpa [a, A, mul_assoc] using hlower
  exact_mod_cast hreal

lemma natCast_mul_reserveProbability_pow_eq_rpow
    {n d s : ℕ} (hn : 0 < n) (hd : 0 < d) (hs : s ≤ d) :
    (n : ℝ) * (reserveProbabilityIcc n d hn : ℝ) ^ s =
      (n : ℝ) ^ (((d - s : ℕ) : ℝ) / d) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : reserveProbability n d ^ s =
      (n : ℝ) ^ (-((s : ℝ) / (d : ℝ))) :=
    reserveProbability_pow_nat hn hd s
  have hexp : (1 : ℝ) - (s : ℝ) / d =
      ((d - s : ℕ) : ℝ) / d := by
    rw [Nat.cast_sub hs]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    field_simp
  change (n : ℝ) * reserveProbability n d ^ s = _
  rw [hp]
  calc
    (n : ℝ) * (n : ℝ) ^ (-((s : ℝ) / d)) =
        (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-((s : ℝ) / d)) := by
          rw [Real.rpow_one]
    _ = (n : ℝ) ^ ((1 : ℝ) - (s : ℝ) / d) := by
      rw [← Real.rpow_add hnR]
      congr 2
    _ = _ := by rw [hexp]

/-- The integer lower branch fits inside the typical lower common-neighbour
bound once the bounded set of already-used vertices costs at most `n/2`. -/
lemma generatorLowerBranching_le_typicalMean
    {n q r d i : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hr : 0 < r) (hrq : r < q) (hqd : Nat.choose q r < d)
    (hnlarge : 2 * (Nat.choose q r * (r - 1)) ≤ n)
    (hi : i < q - r) :
    (generatorLowerBranching d n r i : ℝ) ≤
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
        (reserveProbabilityIcc n d hn : ℝ) ^
          Nat.choose (r + i) (r - 1) / 2 := by
  let s := Nat.choose (r + i) (r - 1)
  have hslt : s < d := extensionRootCount_lt_den hr hrq hi hqd
  have hbranch : (generatorLowerBranching d n r i : ℝ) ≤
      (n : ℝ) ^ (((d - s : ℕ) : ℝ) / d) / 4 := by
    calc
      (generatorLowerBranching d n r i : ℝ) ≤
          (rationalPowerThreshold (d - s) d n : ℝ) / 4 := by
            simpa [generatorLowerBranching, s] using
              (Nat.cast_div_le :
                ((rationalPowerThreshold (d - s) d n / 4 : ℕ) : ℝ) ≤
                  (rationalPowerThreshold (d - s) d n : ℝ) / 4)
      _ ≤ (n : ℝ) ^ (((d - s : ℕ) : ℝ) / d) / 4 :=
        div_le_div_of_nonneg_right
          (rationalPowerThreshold_cast_le (d - s) d n) (by norm_num)
  have hbase : (n : ℝ) / 2 ≤
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : Nat.choose q r * (r - 1) ≤ n)]
    have hcast : (2 : ℝ) *
        ((Nat.choose q r * (r - 1) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hnlarge
    linarith
  have hpnonneg : 0 ≤
      (reserveProbabilityIcc n d hn : ℝ) ^ s :=
    pow_nonneg (reserveProbabilityIcc n d hn).property.1 _
  calc
    (generatorLowerBranching d n r i : ℝ) ≤
        (n : ℝ) ^ (((d - s : ℕ) : ℝ) / d) / 4 := hbranch
    _ = ((n : ℝ) / 2 *
          (reserveProbabilityIcc n d hn : ℝ) ^ s) / 2 := by
      rw [← natCast_mul_reserveProbability_pow_eq_rpow hn hd hslt.le]
      ring
    _ ≤ (((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
          (reserveProbabilityIcc n d hn : ℝ) ^ s) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase hpnonneg) (by norm_num)

/-- Every sampled host edge lies in at least the declared number of
sampled `q`-cliques. -/
theorem generatorCliqueLower_le_cliques_through_edge
    {n q r d : ℕ} (hn : 0 < n) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (hnlarge : 2 * (Nat.choose q r * (r - 1)) ≤ n)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn))
    {e : Finset (Fin n)} (he : e ∈ sampledEdges n r ω) :
    generatorCliqueLower q r d n ≤
      ((cliquesIn n q r (sampledEdges n r ω)).filter fun Q ↦ e ⊆ Q).card := by
  have hd : 0 < d := (Nat.choose_pos hrq.le).trans hqd
  let ell := generatorLowerBranching d n r
  have hell : ∀ i < q - r, (ell i : ℝ) ≤
      ((n - Nat.choose q r * (r - 1) : ℕ) : ℝ) *
        (reserveProbabilityIcc n d hn : ℝ) ^
          Nat.choose (r + i) (r - 1) / 2 := by
    intro i hi
    exact generatorLowerBranching_le_typicalMean hn hd (by omega)
      hrq hqd hnlarge hi
  have hlower := typical_extension_lower_variable hr hrq
    (reserveProbabilityIcc n d hn) ω e ell htyp hell
  have hecard := mem_uniformEdges.mp (mem_sampledEdges.mp he).1
  have htree := reserveCandidates_prod_lower hr hrq.le ell e hecard ω hlower
  have hC : 0 < (2 ^ q) ^ (q - r) := by positivity
  have hdiv :
      (∏ i ∈ Finset.range (q - r), ell i) / (2 ^ q) ^ (q - r) ≤
        (reserveCandidates n q r (sampledEdges n r ω) e).card := by
    apply (Nat.div_le_iff_le_mul hC).2
    exact htree.trans (by omega)
  rw [reserveCandidates_eq_cliquesIn_filter he] at hdiv
  simpa [generatorCliqueLower, ell] using hdiv

/-- For a surviving edge, at least half of the declared clique lower bound
is two-cap unsaturated and hence already generated by the greedy family. -/
theorem twoCapPrunedData_good_card_lower
    {N n q r d : ℕ}
    (D : TwoCapPrunedData N n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      (generatorPruneThreshold q r d n)
      (generatorFaceCliqueCap q r d n)
      (generatorEdgeCliqueCap q r d n))
    (hn : 0 < n) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (hDK : D.K = sampledEdges n r ω)
    (htyp : ∀ roots, ∀ hroots :
      roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn))
    (hnlarge : 2 * (Nat.choose q r * (r - 1)) ≤ n)
    (hthreshold : 2 * generatorPruneThreshold q r d n ≤
      generatorCliqueLower q r d n) :
    ∀ e ∈ D.Kstar,
      generatorCliqueLower q r d n / 2 ≤
        ((twoCapUnsaturatedCliques n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          D.K D.selected).filter fun Q ↦ e ⊆ Q).card := by
  intro e he
  have heK : e ∈ D.K := D.Kstar_subset he
  have heSample : e ∈ sampledEdges n r ω := by simpa [← hDK]
  have htotal : generatorCliqueLower q r d n ≤
      ((cliquesIn n q r D.K).filter fun Q ↦ e ⊆ Q).card := by
    simpa [hDK] using generatorCliqueLower_le_cliques_through_edge
      hn hr hrq hqd hnlarge ω htyp heSample
  have hsub : generatorCliqueLower q r d n / 2 ≤
      ((cliquesIn n q r D.K).filter fun Q ↦ e ⊆ Q).card -
        generatorPruneThreshold q r d n := by omega
  exact hsub.trans (D.good_lower e he)

lemma generatorDegreeLower_le_typicalMean
    {n r d : ℕ} (hn : 0 < n) (hd : 1 < d)
    (hnlarge : 2 * (r - 1) ≤ n) :
    (generatorDegreeLower d n : ℝ) ≤
      ((n - (r - 1) : ℕ) : ℝ) *
        (reserveProbabilityIcc n d hn : ℝ) / 2 := by
  have hdegree : (generatorDegreeLower d n : ℝ) ≤
      (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 4 := by
    calc
      (generatorDegreeLower d n : ℝ) ≤
          (rationalPowerThreshold (d - 1) d n : ℝ) / 4 := by
            simpa [generatorDegreeLower] using
              (Nat.cast_div_le :
                ((rationalPowerThreshold (d - 1) d n / 4 : ℕ) : ℝ) ≤
                  (rationalPowerThreshold (d - 1) d n : ℝ) / 4)
      _ ≤ (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 4 :=
        div_le_div_of_nonneg_right
          (rationalPowerThreshold_cast_le (d - 1) d n) (by norm_num)
  have hbase : (n : ℝ) / 2 ≤ ((n - (r - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : r - 1 ≤ n)]
    have hcast : (2 : ℝ) * ((r - 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hnlarge
    linarith
  have hpnonneg : 0 ≤ (reserveProbabilityIcc n d hn : ℝ) :=
    (reserveProbabilityIcc n d hn).property.1
  calc
    (generatorDegreeLower d n : ℝ) ≤
        (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 4 := hdegree
    _ = ((n : ℝ) / 2 * (reserveProbabilityIcc n d hn : ℝ)) / 2 := by
      rw [← natCast_mul_reserveProbability_pow_eq_rpow
        hn (by omega : 0 < d) (by omega : 1 ≤ d)]
      simp
      ring
    _ ≤ (((n - (r - 1) : ℕ) : ℝ) *
        (reserveProbabilityIcc n d hn : ℝ)) / 2 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase hpnonneg) (by norm_num)

/-- Eventual construction of the pruned modular-generator host, retaining
at least half of the simultaneously typical Bernoulli sample. -/
theorem eventually_exists_prunedGeneratorSample
    (N q r d : ℕ) (hN : 0 < N) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 0 < n,
      ∃ ω : {e // e ∈ uniformEdges n r} → Bool,
      ∃ D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n),
        (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
          commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
            Erdos722.Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots (by omega)
                (root_card_of_mem_rootFamilies hroots) x) ω ∧
          Erdos722.Probability.finiteRandomSum
              (fun x ↦ commonNeighborIndicator n r roots (by omega)
                (root_card_of_mem_rootFamilies hroots) x) ω <
            2 * commonMean n roots (reserveProbabilityIcc n d hn)) ∧
        D.K = sampledEdges n r ω ∧
        D.K.card ≤ 2 * D.Kstar.card ∧
        (∀ e ∈ D.Kstar,
          generatorCliqueLower q r d n / 2 ≤
            ((twoCapUnsaturatedCliques n q r
              (generatorFaceCap d n) (generatorEdgeCap d n)
              D.K D.selected).filter fun Q ↦ e ⊆ Q).card) ∧
        (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
          2 * D.Kstar.card * Nat.choose r (r - 1) := by
  have hKpos : 0 < Nat.choose q r := Nat.choose_pos hrq.le
  have hd : 0 < d := hKpos.trans hqd
  have hthresholdNumerator :
      Nat.choose q r - 1 < d * (q - r) := by
    have hm : 0 < q - r := by omega
    exact (by omega : Nat.choose q r - 1 < d).trans_le
      (Nat.le_mul_of_pos_right d hm)
  filter_upwards [eventually_exists_uncolored_typical_sample
      r (Nat.choose q r) d (by omega) hd hqd,
    eventually_generator_pruning_scalar N q r d (by omega) hrq hqd,
    generatorFaceCap_pos_eventually hd,
    generatorEdgeCap_pos_eventually hd,
    generatorPruneThreshold_pos_eventually hrq hthresholdNumerator hd,
    eventually_two_mul_generatorPruneThreshold_le_cliqueLower
      q r d (by omega) hrq hqd,
    eventually_ge_atTop (2 * (Nat.choose q r * (r - 1)))]
      with n hsample hscalar hfacePos hedgePos hthresholdPos
        hthresholdSmall hnlarge
  obtain ⟨hn, ω, htyp⟩ := hsample
  obtain ⟨D, hDK⟩ := exists_generatorTwoCapPrunedData
    hN hn hr hrq ω htyp
  have hloss :
      2 * ((N * D.K.card) *
        (Nat.choose q (r - 1) * generatorEdgeCap d n *
            generatorFaceCliqueCap q r d n +
          Nat.choose q r * generatorFaceCap d n *
            generatorEdgeCliqueCap q r d n) * Nat.choose q r) ≤
        generatorFaceCap d n * generatorEdgeCap d n *
          generatorPruneThreshold q r d n * D.K.card := by
    have hmul := Nat.mul_le_mul_right D.K.card hscalar
    calc
      2 * ((N * D.K.card) *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
              generatorFaceCliqueCap q r d n +
            Nat.choose q r * generatorFaceCap d n *
              generatorEdgeCliqueCap q r d n) * Nat.choose q r) =
        (2 * N *
          (Nat.choose q (r - 1) * generatorEdgeCap d n *
              generatorFaceCliqueCap q r d n +
            Nat.choose q r * generatorFaceCap d n *
              generatorEdgeCliqueCap q r d n) * Nat.choose q r) *
            D.K.card := by ring
      _ ≤ (generatorFaceCap d n * generatorEdgeCap d n *
          generatorPruneThreshold q r d n) * D.K.card := hmul
      _ = generatorFaceCap d n * generatorEdgeCap d n *
          generatorPruneThreshold q r d n * D.K.card := by ring
  have hhalf := D.card_K_le_two_mul_card_Kstar
    hfacePos hedgePos hthresholdPos hloss
  have hgood := twoCapPrunedData_good_card_lower D hn hr hrq hqd ω hDK htyp
    hnlarge hthresholdSmall
  have hnlargeDegree : 2 * (r - 1) ≤ n := by
    calc
      2 * (r - 1) ≤ 2 * (Nat.choose q r * (r - 1)) :=
        Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_left (r - 1) hKpos)
      _ ≤ n := hnlarge
  have hdegreeMean := generatorDegreeLower_le_typicalMean hn
    (by omega : 1 < d) hnlargeDegree
  have hrootLower := typical_rootEdges_lower (q := q) (L := generatorDegreeLower d n)
    (by omega : 0 < r) hrq.le (reserveProbabilityIcc n d hn) ω htyp hdegreeMean
  have hrootLowerD : ∀ f ∈ uniformEdges n (r - 1),
      generatorDegreeLower d n ≤ (rootEdges D.K f).card := by
    simpa [hDK] using hrootLower
  have hincidence := card_uniformEdges_mul_lower_le_card_mul_choose
    D.uniform hrootLowerD
  have hglobal :
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) := by
    exact hincidence.trans (Nat.mul_le_mul_right _ hhalf)
  exact ⟨hn, ω, D, htyp, hDK, hhalf, hgood, hglobal⟩

end

end Erdos722.GeneratorAsymptotic
