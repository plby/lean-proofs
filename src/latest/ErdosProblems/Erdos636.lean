/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 636.
https://www.erdosproblems.com/forum/thread/636

Informal authors:
- Matthew Kwan
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos636.md
-/
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

import ErdosProblems.Erdos88.Richness
import ErdosProblems.Erdos88.Esseen
import ErdosProblems.Erdos636.FiniteChoice
import ErdosProblems.Erdos636.KwanSudakov
import ErdosProblems.Erdos636.OuterAssembly
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Erdős Problem 636

Kwan and Sudakov proved that every `C`-Ramsey graph on `n` vertices has
`Ω_C(n ^ (5 / 2))` induced-subgraph profiles.  A profile records both the
number of vertices and the number of edges.  The public theorem below uses
the exactly equivalent scale `n ^ 2 * sqrt n`.

Primary source: M. Kwan and B. Sudakov, *Proof of a conjecture on induced
subgraphs of Ramsey graphs*, Theorem 1.1, arXiv:1712.05656.
-/

open Classical SimpleGraph
open MeasureTheory ProbabilityTheory

namespace Erdos636

/-- The pair consisting of the order and size of an induced subgraph. -/
noncomputable def inducedProfile {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℕ × ℕ :=
  (S.card, Erdos88.inducedEdges G S)

/-- All induced-subgraph profiles of `G`. -/
noncomputable def inducedProfiles {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image (inducedProfile G)

@[simp] lemma mem_inducedProfiles {n : ℕ} {G : SimpleGraph (Fin n)}
    {p : ℕ × ℕ} :
    p ∈ inducedProfiles G ↔ ∃ S : Finset (Fin n), inducedProfile G S = p := by
  simp [inducedProfiles]

lemma inducedProfile_fst {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    (inducedProfile G S).1 = S.card := rfl

lemma inducedProfile_snd {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) :
    (inducedProfile G S).2 = Erdos88.inducedEdges G S := rfl

/-- Edge counts of induced subgraphs on exactly `k` vertices. -/
noncomputable def edgeProfilesAt {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Finset ℕ :=
  (Finset.univ.filter fun S : Finset (Fin n) ↦ S.card = k).image
    (Erdos88.inducedEdges G)

@[simp] lemma mem_edgeProfilesAt {n k m : ℕ} {G : SimpleGraph (Fin n)} :
    m ∈ edgeProfilesAt G k ↔
      ∃ S : Finset (Fin n), S.card = k ∧ Erdos88.inducedEdges G S = m := by
  simp [edgeProfilesAt]

lemma profile_mk_mem_iff {n k m : ℕ} {G : SimpleGraph (Fin n)} :
    (k, m) ∈ inducedProfiles G ↔ m ∈ edgeProfilesAt G k := by
  simp [inducedProfile]

/-- The profiles whose first coordinate is the fixed order `k`. -/
noncomputable def profileSlice {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    Finset (ℕ × ℕ) :=
  (edgeProfilesAt G k).image fun m ↦ (k, m)

@[simp] lemma mem_profileSlice {n k : ℕ} {G : SimpleGraph (Fin n)}
    {p : ℕ × ℕ} :
    p ∈ profileSlice G k ↔ p.1 = k ∧ p.2 ∈ edgeProfilesAt G k := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
    simp only [Prod.fst, Prod.snd, true_and]
    exact hm
  · rintro ⟨hp, hm⟩
    apply Finset.mem_image.mpr
    exact ⟨p.2, hm, Prod.ext hp.symm rfl⟩

@[simp] lemma card_profileSlice {n k : ℕ} (G : SimpleGraph (Fin n)) :
    (profileSlice G k).card = (edgeProfilesAt G k).card := by
  classical
  rw [profileSlice, Finset.card_image_iff.mpr]
  intro a _ha b _hb hab
  exact congrArg Prod.snd hab

lemma profileSlice_subset_inducedProfiles {n k : ℕ} (G : SimpleGraph (Fin n)) :
    profileSlice G k ⊆ inducedProfiles G := by
  intro p hp
  rw [mem_profileSlice] at hp
  rw [← Prod.eta p, hp.1, profile_mk_mem_iff]
  exact hp.2

lemma profileSlice_pairwiseDisjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Finset ℕ) :
    (I : Set ℕ).PairwiseDisjoint (profileSlice G) := by
  intro k _hk l _hl hkl
  change Disjoint (profileSlice G k) (profileSlice G l)
  rw [Finset.disjoint_left]
  intro p hpk hpl
  have hk : p.1 = k := (mem_profileSlice.mp hpk).1
  have hl : p.1 = l := (mem_profileSlice.mp hpl).1
  exact hkl (hk.symm.trans hl)

/-- Fixed-order spectra inject into the global profile spectrum, and spectra
of different orders are disjoint. -/
lemma sum_card_edgeProfilesAt_le_inducedProfiles {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset ℕ) :
    ∑ k ∈ I, (edgeProfilesAt G k).card ≤ (inducedProfiles G).card := by
  classical
  calc
    ∑ k ∈ I, (edgeProfilesAt G k).card =
        ∑ k ∈ I, (profileSlice G k).card := by simp
    _ = (I.biUnion (profileSlice G)).card :=
      (Finset.card_biUnion (profileSlice_pairwiseDisjoint G I)).symm
    _ ≤ (inducedProfiles G).card := by
      apply Finset.card_le_card
      intro p hp
      rcases Finset.mem_biUnion.mp hp with ⟨k, _hk, hpk⟩
      exact profileSlice_subset_inducedProfiles G hpk

/-- Every tagged collection of fixed-order edge spectra consists of genuine
induced-subgraph profiles.  This is the containment needed by the generic
bounded-multiplicity outer assembly. -/
lemma taggedSpectra_edgeProfilesAt_subset_inducedProfiles {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset ℕ) :
    ProfileReduction.taggedSpectra I (edgeProfilesAt G) ⊆ inducedProfiles G := by
  intro p hp
  rcases Finset.mem_biUnion.mp hp with ⟨k, _hk, hpk⟩
  have hpk' := ProfileReduction.mem_taggedSpectrum.mp hpk
  rw [← Prod.eta p, hpk'.1, profile_mk_mem_iff]
  exact hpk'.2

/-- A family of vertex sets is distinguished by order or size exactly when
the profile map is injective on it. -/
def IsProfileInjectiveFamily {n : ℕ} (G : SimpleGraph (Fin n))
    (F : Finset (Finset (Fin n))) : Prop :=
  Set.InjOn (inducedProfile G) (F : Set (Finset (Fin n)))

lemma card_family_le_profiles {n : ℕ} {G : SimpleGraph (Fin n)}
    {F : Finset (Finset (Fin n))} (hF : IsProfileInjectiveFamily G F) :
    F.card ≤ (inducedProfiles G).card := by
  classical
  calc
    F.card = (F.image (inducedProfile G)).card := by
      symm
      apply Finset.card_image_iff.mpr
      intro S hS T hT hST
      exact hF (by simpa using hS) (by simpa using hT) hST
    _ ≤ (inducedProfiles G).card := by
      apply Finset.card_le_card
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨S, hS, rfl⟩
      simp [inducedProfiles]

/-- Conversely, one can choose exactly one induced subgraph representing
each attained profile.  Thus `inducedProfiles.card` is not merely an upper
bound: it is the maximum size of a pairwise profile-distinguished family. -/
lemma exists_profileInjectiveFamily_card_eq_profiles {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    ∃ F : Finset (Finset (Fin n)),
      IsProfileInjectiveFamily G F ∧ F.card = (inducedProfiles G).card := by
  obtain ⟨F, _hsub, hF, hcard⟩ :=
    exists_subset_injOn_card_eq_card_image
      (Finset.univ : Finset (Finset (Fin n))) (inducedProfile G)
  refine ⟨F, hF, ?_⟩
  rw [hcard]
  congr 1
  ext p
  simp [inducedProfiles]

/-! ## The population-variance repair to the published local lemma -/

/-- Squared mass of a coefficient population after centering at `μ`. -/
noncomputable def centeredMass {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (μ : ℝ) : ℝ :=
  ∑ i ∈ s, (a i - μ) ^ 2

lemma centeredMass_nonneg {ι : Type*} (s : Finset ι) (a : ι → ℝ) (μ : ℝ) :
    0 ≤ centeredMass s a μ := by
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- If a centered bounded-integer coefficient population has linear
`ℓ¹`-mass, then either its sum is linear or its centered variance mass is
linear.  This is the nondegeneracy dichotomy needed to repair the omitted
variance hypothesis in the printed Kwan--Sudakov local lemma. -/
lemma abs_sum_or_centeredMass_ge {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (μ θ : ℝ) (hs : s.Nonempty) (hθ : 0 ≤ θ)
    (hmean : (s.card : ℝ) * μ = ∑ i ∈ s, a i)
    (hl1 : θ * s.card ≤ ∑ i ∈ s, |a i|) :
    θ / 2 * s.card ≤ |∑ i ∈ s, a i| ∨
      θ ^ 2 / 4 * s.card ≤ centeredMass s a μ := by
  classical
  by_cases hlarge : θ / 2 * s.card ≤ |∑ i ∈ s, a i|
  · exact Or.inl hlarge
  · right
    have hm : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
    have hmeanAbs : (s.card : ℝ) * |μ| = |∑ i ∈ s, a i| := by
      have hcardAbs : |(s.card : ℝ)| = (s.card : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg s.card)
      calc
        (s.card : ℝ) * |μ| = |(s.card : ℝ) * μ| := by
          rw [abs_mul, hcardAbs]
        _ = |∑ i ∈ s, a i| := congrArg abs hmean
    have htriangle :
        ∑ i ∈ s, |a i| ≤
          (s.card : ℝ) * |μ| + ∑ i ∈ s, |a i - μ| := by
      calc
        ∑ i ∈ s, |a i| ≤ ∑ i ∈ s, (|μ| + |a i - μ|) := by
          apply Finset.sum_le_sum
          intro i hi
          calc
            |a i| = |μ + (a i - μ)| := by congr 1 <;> ring
            _ ≤ |μ| + |a i - μ| := abs_add_le _ _
        _ = (s.card : ℝ) * |μ| + ∑ i ∈ s, |a i - μ| := by
          simp [Finset.sum_add_distrib]
    have hdiff : θ / 2 * s.card < ∑ i ∈ s, |a i - μ| := by
      rw [hmeanAbs] at htriangle
      have hnot : |∑ i ∈ s, a i| < θ / 2 * s.card := lt_of_not_ge hlarge
      linarith
    have hcauchy :
        (∑ i ∈ s, |a i - μ|) ^ 2 ≤
          (s.card : ℝ) * centeredMass s a μ := by
      simpa only [sq_abs, centeredMass] using
        (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ |a i - μ|))
    have htargetSq :
        (θ / 2 * (s.card : ℝ)) ^ 2 ≤
          (s.card : ℝ) * centeredMass s a μ := by
      have hsquare :=
        (sq_le_sq₀ (by positivity)
          (Finset.sum_nonneg fun i _ ↦ abs_nonneg (a i - μ))).2 hdiff.le
      exact hsquare.trans hcauchy
    nlinarith [centeredMass_nonneg s a μ]

/-- Restricting a nonnegative Gaussian to a symmetric finite interval can
only decrease its integral.  This is the final analytic estimate used after
Esseen's inequality. -/
lemma intervalIntegral_exp_neg_mul_sq_le {b L : ℝ} (hb : 0 < b)
    (hL : 0 ≤ L) :
    (∫ t : ℝ in -L..L, Real.exp (-b * t ^ 2)) ≤ Real.sqrt (Real.pi / b) := by
  rw [intervalIntegral.integral_of_le (by linarith)]
  calc
    (∫ t : ℝ in Set.Ioc (-L) L, Real.exp (-b * t ^ 2)) ≤
        ∫ t : ℝ, Real.exp (-b * t ^ 2) :=
      MeasureTheory.setIntegral_le_integral (integrable_exp_neg_mul_sq hb)
        (Filter.Eventually.of_forall fun t ↦ (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / b) := integral_gaussian b

/-! ### Uniform finite laws and the checked Esseen theorem -/

/-- Push-forward to `ℝ` of uniform counting measure on a nonempty finite
sample space. -/
noncomputable def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) : Measure ℝ :=
  ((PMF.uniformOfFintype Ω).map X).toMeasure

noncomputable instance uniformLaw.instIsProbabilityMeasure
    (Ω : Type*) [Fintype Ω] [Nonempty Ω] (X : Ω → ℝ) :
    IsProbabilityMeasure (uniformLaw Ω X) := by
  unfold uniformLaw
  infer_instance

lemma charFun_uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (t : ℝ) :
    charFun (uniformLaw Ω X) t = Erdos88.Fourier.finCharFun Ω X t := by
  let : MeasurableSpace Ω := ⊤
  let : MeasurableSingletonClass Ω := ⟨fun _ ↦ MeasurableSet.of_discrete⟩
  rw [uniformLaw, ← PMF.toMeasure_map (p := PMF.uniformOfFintype Ω) (f := X)
    (measurable_of_finite X), charFun_apply_real, integral_map]
  · rw [PMF.integral_eq_sum]
    simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      Erdos88.Fourier.finCharFun, Erdos88.Fourier.finExpectation]
    simp only [smul_eq_mul, div_eq_mul_inv]
    rw [mul_comm (∑ ω, Complex.exp (((t * X ω : ℝ) : ℂ) * Complex.I))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Complex.real_smul, mul_comm]
    push_cast
    ring
  · fun_prop
  · fun_prop

lemma uniformLaw_real_apply (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    (uniformLaw Ω X).real s =
      ((Finset.univ.filter fun ω ↦ X ω ∈ s).card : ℝ) / Fintype.card Ω := by
  let : MeasurableSpace Ω := ⊤
  let : MeasurableSingletonClass Ω := ⟨fun _ ↦ MeasurableSet.of_discrete⟩
  rw [uniformLaw, ← PMF.toMeasure_map (p := PMF.uniformOfFintype Ω) (f := X)
    (measurable_of_finite X), Measure.real, Measure.map_apply
      (measurable_of_finite X) hs]
  rw [PMF.toMeasure_uniformOfFintype_apply (s := X ⁻¹' s)
    (measurableSet_preimage (measurable_of_finite X) hs)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 1
  exact_mod_cast Fintype.card_subtype (fun ω : Ω ↦ X ω ∈ s)

/-- Every point event is contained in a positive-radius small ball under the
uniform push-forward law. -/
lemma finProbability_eq_le_smallBall (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    Erdos88.Fourier.finProbability Ω (fun ω ↦ X ω = x) ≤
      Erdos88.Esseen.smallBall (uniformLaw Ω X) eps x := by
  rw [Erdos88.Fourier.finProbability, Erdos88.Esseen.smallBall,
    uniformLaw_real_apply Ω X _ measurableSet_Icc]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      constructor <;> rw [hω] <;> linarith)
  · positivity

/-! ### A checked fixed-slice anti-concentration input -/

/-- The real linear statistic on a Boolean slice whose characteristic
function is `sliceCharFun`. -/
noncomputable def sliceLinear {I : Type*} [Fintype I] [DecidableEq I]
    (s : ℕ) (a : I → ℝ) (x : Erdos88.Fourier.BoolSlice I s) : ℝ :=
  ∑ i, a i * if x.1 i then 1 else 0

lemma charFun_uniformLaw_sliceLinear {I : Type*} [Fintype I] [DecidableEq I]
    (s : ℕ) [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (a : I → ℝ) (t : ℝ) :
    charFun (uniformLaw (Erdos88.Fourier.BoolSlice I s) (sliceLinear s a)) t =
      Erdos88.Fourier.sliceCharFun s a t := by
  exact charFun_uniformLaw _ _ _

/-- On the low-frequency interval, linearly many disjoint coefficient pairs
whose differences lie in `[1,B]` force Gaussian decay of the characteristic
function.  This is the analytic core used in the three local-limit
applications of Kwan--Sudakov. -/
lemma norm_sliceCharFun_le_gaussian_of_pairs
    {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (p : Erdos88.Fourier.PairEmbedding K I) (s : ℕ)
    [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (a : I → ℝ) (c B t : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hdiffLower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hdiffUpper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (ht : |t| ≤ 1 / (4 * B)) :
    ‖Erdos88.Fourier.sliceCharFun s a t‖ ≤
      Real.exp 1 * Real.exp (-(c ^ 3 / 256) * Fintype.card K *
        (|t| / (2 * Real.pi)) ^ 2) := by
  let delta : ℝ := |t| / (2 * Real.pi)
  let q : K → ℝ := fun k ↦
    t * (a (p (k, false)) - a (p (k, true))) / (2 * Real.pi)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hfourB : 0 < 4 * B := mul_pos (by norm_num) hB0
  have hquarter : 1 / (4 * B) ≤ (1 / 4 : ℝ) := by
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have htquarter : |t| ≤ (1 / 4 : ℝ) := ht.trans hquarter
  apply Erdos88.Fourier.norm_sliceCharFun_le_balanced p s a t delta c q
  · exact hc0
  · exact hc1
  · exact hsel
  · exact hunsel
  · exact div_nonneg (abs_nonneg t) htwoPi.le
  · apply (div_le_iff₀ htwoPi).2
    nlinarith [Real.pi_gt_three]
  · intro k
    refine ⟨?_, 0, ?_⟩
    · dsimp only [q]
      rw [abs_div, abs_mul, abs_of_pos htwoPi]
      apply (div_le_iff₀ htwoPi).2
      have hmul :
          |t| * |a (p (k, false)) - a (p (k, true))| ≤
            (1 / (4 * B)) * B :=
        mul_le_mul ht (hdiffUpper k) (abs_nonneg _)
          (by positivity)
      have hmul' :
          |t| * |a (p (k, false)) - a (p (k, true))| ≤ 1 / 4 := by
        convert hmul using 1 <;> field_simp [ne_of_gt hB0]
      nlinarith [Real.pi_gt_three]
    · dsimp only [q]
      push_cast
      ring
  · intro k
    dsimp only [delta, q]
    rw [abs_div, abs_mul, abs_of_pos htwoPi]
    apply div_le_div_of_nonneg_right _ htwoPi.le
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hdiffLower k) (abs_nonneg t)

/-- Esseen plus the preceding characteristic-function estimate gives a
fully checked point-mass bound.  The displayed rate is positive and linear
in the number of separated pairs, hence the right-hand side is
`O(1 / sqrt |K|)` for fixed `c,B`. -/
lemma slice_point_probability_le_of_pairs
    {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (p : Erdos88.Fourier.PairEmbedding K I) (s : ℕ)
    [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (a : I → ℝ) (c B : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hdiffLower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hdiffUpper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (hK : 0 < Fintype.card K) (x : ℝ) :
    Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice I s)
        (fun ω ↦ sliceLinear s a ω = x) ≤
      16 * B * Real.exp 1 *
        Real.sqrt (Real.pi /
          ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2))) := by
  let rate : ℝ := (c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2)
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have heps : 0 < 8 * B := mul_pos (by norm_num) hB0
  have hrate : 0 < rate := by
    dsimp only [rate]
    positivity
  have hcharIntegral :
      (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          ‖charFun
            (uniformLaw (Erdos88.Fourier.BoolSlice I s) (sliceLinear s a)) t‖) ≤
        ∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp 1 * Real.exp (-rate * t ^ 2) := by
    apply intervalIntegral.integral_mono_on
      (neg_le_self (by positivity))
      ((continuous_norm.comp continuous_charFun).intervalIntegrable _ _)
      ((continuous_const.mul
        (Real.continuous_exp.comp (by fun_prop))).intervalIntegrable _ _)
    intro t htIcc
    have ht' : |t| ≤ 1 / (4 * B) := by
      calc
        |t| ≤ 2 / (8 * B) := (abs_le).2 htIcc
        _ = 1 / (4 * B) := by field_simp [ne_of_gt hB0] <;> ring
    change ‖charFun
      (uniformLaw (Erdos88.Fourier.BoolSlice I s) (sliceLinear s a)) t‖ ≤
        Real.exp 1 * Real.exp (-rate * t ^ 2)
    rw [charFun_uniformLaw_sliceLinear]
    calc
      ‖Erdos88.Fourier.sliceCharFun s a t‖ ≤
          Real.exp 1 * Real.exp (-(c ^ 3 / 256) * Fintype.card K *
            (|t| / (2 * Real.pi)) ^ 2) :=
        norm_sliceCharFun_le_gaussian_of_pairs p s a c B t hc0 hc1
          hsel hunsel hB hdiffLower hdiffUpper ht'
      _ = Real.exp 1 * Real.exp (-rate * t ^ 2) := by
        congr 2
        dsimp only [rate]
        rw [div_pow, sq_abs]
        ring
  calc
    Erdos88.Fourier.finProbability (Erdos88.Fourier.BoolSlice I s)
        (fun ω ↦ sliceLinear s a ω = x) ≤
        Erdos88.Esseen.smallBall
          (uniformLaw (Erdos88.Fourier.BoolSlice I s) (sliceLinear s a))
          (8 * B) x := finProbability_eq_le_smallBall _ _ _ heps x
    _ ≤ 2 * (8 * B) *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          ‖charFun
            (uniformLaw (Erdos88.Fourier.BoolSlice I s) (sliceLinear s a)) t‖) :=
      Erdos88.Esseen.esseen_4_7 _ heps x
    _ ≤ 2 * (8 * B) *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp 1 * Real.exp (-rate * t ^ 2)) :=
      mul_le_mul_of_nonneg_left hcharIntegral (by positivity)
    _ = 16 * B * Real.exp 1 *
        (∫ t : ℝ in -(2 / (8 * B))..(2 / (8 * B)),
          Real.exp (-rate * t ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ 16 * B * Real.exp 1 * Real.sqrt (Real.pi / rate) := by
      apply mul_le_mul_of_nonneg_left
        (intervalIntegral_exp_neg_mul_sq_le hrate (by positivity))
      positivity
    _ = 16 * B * Real.exp 1 *
        Real.sqrt (Real.pi /
          ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2))) := rfl

/-- If every fibre of a map on a uniform finite probability space has mass
at most `P`, then the image contains at least `1/P` values.  The product
form avoids any positivity side condition on `P`. -/
lemma one_le_card_image_mul_of_finProbability_le
    (Ω : Type*) [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (P : ℝ)
    (hP : ∀ y : ℝ,
      Erdos88.Fourier.finProbability Ω (fun ω ↦ X ω = y) ≤ P) :
    1 ≤ ((Finset.univ.image X).card : ℝ) * P := by
  classical
  let ys : Finset ℝ := Finset.univ.image X
  let fib : ℝ → Finset Ω := fun y ↦ Finset.univ.filter fun ω ↦ X ω = y
  have hdisj : (ys : Set ℝ).PairwiseDisjoint fib := by
    intro y _hy z _hz hyz
    change Disjoint (fib y) (fib z)
    rw [Finset.disjoint_left]
    intro ω hωy hωz
    have hxy : X ω = y := by simpa [fib] using hωy
    have hxz : X ω = z := by simpa [fib] using hωz
    exact hyz (hxy.symm.trans hxz)
  have hunion : ys.biUnion fib = (Finset.univ : Finset Ω) := by
    ext ω
    simp [ys, fib]
  have hpartition :
      Fintype.card Ω = ∑ y ∈ ys, (fib y).card := by
    rw [← Finset.card_univ, ← hunion, Finset.card_biUnion hdisj]
  have hcardpos : (0 : ℝ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  have hfib : ∀ y : ℝ, ((fib y).card : ℝ) ≤ P * Fintype.card Ω := by
    intro y
    apply (div_le_iff₀ hcardpos).1
    simpa only [fib, Erdos88.Fourier.finProbability] using hP y
  have hpartitionR :
      (Fintype.card Ω : ℝ) = ∑ y ∈ ys, ((fib y).card : ℝ) := by
    exact_mod_cast hpartition
  have htotal :
      (Fintype.card Ω : ℝ) ≤
        ((ys.card : ℝ) * P) * Fintype.card Ω := by
    calc
      (Fintype.card Ω : ℝ) = ∑ y ∈ ys, ((fib y).card : ℝ) := hpartitionR
      _ ≤ ∑ _y ∈ ys, P * Fintype.card Ω :=
        Finset.sum_le_sum fun y _hy ↦ hfib y
      _ = ((ys.card : ℝ) * P) * Fintype.card Ω := by
        simp
        ring
  change 1 ≤ (ys.card : ℝ) * P
  nlinarith

/-- Support-size form of the checked slice anti-concentration theorem. -/
lemma one_le_card_sliceLinear_image_mul_gaussian
    {K I : Type*} [Fintype K] [DecidableEq K]
    [Fintype I] [DecidableEq I]
    (p : Erdos88.Fourier.PairEmbedding K I) (s : ℕ)
    [Nonempty (Erdos88.Fourier.BoolSlice I s)]
    (a : I → ℝ) (c B : ℝ)
    (hc0 : 0 < c) (hc1 : c ≤ 1 / 2)
    (hsel : c * Fintype.card I ≤ s)
    (hunsel : c * Fintype.card I ≤ Fintype.card I - s)
    (hB : 1 ≤ B)
    (hdiffLower : ∀ k, 1 ≤ |a (p (k, false)) - a (p (k, true))|)
    (hdiffUpper : ∀ k, |a (p (k, false)) - a (p (k, true))| ≤ B)
    (hK : 0 < Fintype.card K) :
    1 ≤
      ((Finset.univ.image (sliceLinear s a)).card : ℝ) *
        (16 * B * Real.exp 1 *
          Real.sqrt (Real.pi /
            ((c ^ 3 / 256) * Fintype.card K / (4 * Real.pi ^ 2)))) := by
  apply one_le_card_image_mul_of_finProbability_le
  intro x
  exact slice_point_probability_le_of_pairs p s a c B hc0 hc1 hsel hunsel
    hB hdiffLower hdiffUpper hK x

/-- A fixed-order spectrum conclusion strong enough for the final summation:
linearly many orders each support order `n * sqrt n` distinct edge counts. -/
def HasLargeFixedOrderSpectra (C : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
    ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
      ∃ I : Finset ℕ,
        c * n ≤ I.card ∧
          ∀ k ∈ I,
            c * n * Real.sqrt n ≤ (edgeProfilesAt G k).card

/-- The purely finite summation which converts the fixed-order conclusion
into the `n^2 * sqrt n` global profile bound. -/
lemma erdos636_of_fixedOrderSpectra {C : ℝ} (hC : HasLargeFixedOrderSpectra C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (inducedProfiles G).card := by
  rcases hC with ⟨c, hc, N, hN⟩
  refine ⟨c ^ 2, sq_pos_of_pos hc, N, ?_⟩
  intro n hn G hG
  rcases hN n hn G hG with ⟨I, hI, hslice⟩
  have hscale : 0 ≤ c * (n : ℝ) * Real.sqrt n := by positivity
  have hsum :
      ∑ k ∈ I, c * (n : ℝ) * Real.sqrt n ≤
        ∑ k ∈ I, ((edgeProfilesAt G k).card : ℝ) := by
    exact Finset.sum_le_sum fun k hk ↦ hslice k hk
  have hglobal :
      (∑ k ∈ I, ((edgeProfilesAt G k).card : ℝ)) ≤
        ((inducedProfiles G).card : ℝ) := by
    exact_mod_cast sum_card_edgeProfilesAt_le_inducedProfiles G I
  calc
    c ^ 2 * (n : ℝ) ^ 2 * Real.sqrt n =
        (c * n) * (c * n * Real.sqrt n) := by ring
    _ ≤ (I.card : ℝ) * (c * n * Real.sqrt n) :=
      mul_le_mul_of_nonneg_right hI hscale
    _ = ∑ _k ∈ I, c * n * Real.sqrt n := by simp
    _ ≤ ∑ k ∈ I, ((edgeProfilesAt G k).card : ℝ) := hsum
    _ ≤ ((inducedProfiles G).card : ℝ) := hglobal

/-- Once the fully rounded Kwan--Sudakov structural/augmentation assembly is
available, the exact theorem follows by the checked bounded-multiplicity
counting argument. -/
theorem erdos636_of_hasRoundedAssembly (C : ℝ)
    (h : OuterAssembly.HasRoundedAssembly
      (Ambient := fun n ↦ SimpleGraph (Fin n))
      (fun _n G ↦ Erdos88.RamseyFree C G)
      (fun _n G ↦ edgeProfilesAt G)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (inducedProfiles G).card := by
  apply OuterAssembly.globalProfileLowerBound_of_hasBoundedMultiplicitySpectra
    (OuterAssembly.hasBoundedMultiplicitySpectra_of_hasRoundedAssembly h)
  intro n G I
  exact taggedSpectra_edgeProfilesAt_subset_inducedProfiles G I

/-! ## The Kwan--Sudakov theorem and the public resolution -/

/-- The graph-facing fixed-order spectrum used by the augmentation modules
is definitionally the fixed-order spectrum used in this public file. -/
@[simp] lemma fixedOrderEdgeValues_eq_edgeProfilesAt {n k : ℕ}
    (G : SimpleGraph (Fin n)) :
    Augmentation.fixedOrderEdgeValues G k = edgeProfilesAt G k := rfl

/-- Checked reduction from the pointwise-window conclusion to the base-two
profile-count theorem. -/
theorem erdos636_profile_count_ramseyFree_of_pointwiseWindows (C : ℝ)
    (hKS : KwanSudakov.RamseyFreePointwiseWindows C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (inducedProfiles G).card := by
  have hrounded : OuterAssembly.HasRoundedAssembly
      (Ambient := fun n ↦ SimpleGraph (Fin n))
      (fun _n G ↦ Erdos88.RamseyFree C G)
      (fun _n G ↦ edgeProfilesAt G) := by
    change OuterAssembly.HasRoundedAssembly
      (Ambient := fun n ↦ SimpleGraph (Fin n))
      (fun _n G ↦ Erdos88.RamseyFree C G)
      (fun _n G ↦ Augmentation.fixedOrderEdgeValues G)
    exact KwanSudakov.hasRoundedAssembly_ramseyFree_of_pointwiseWindows hKS
  exact erdos636_of_hasRoundedAssembly C hrounded

/-- Base-two form of the Kwan--Sudakov profile-count theorem.  The sole deep
input is `KwanSudakov.ramseyFreePointwiseWindows`; all subsequent rounding,
bounded-multiplicity, and profile-counting steps are checked reductions. -/
theorem erdos636_profile_count_ramseyFree (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (inducedProfiles G).card :=
  erdos636_profile_count_ramseyFree_of_pointwiseWindows C
    (KwanSudakov.ramseyFreePointwiseWindows C hC)

/-- Natural-log form of the resolved profile-count problem: a graph with no
clique or independent set of size at least `C * log n` has
`Omega_C(n^2 * sqrt n)` distinct induced-subgraph profiles. -/
theorem erdos636_profile_count (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (inducedProfiles G).card := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases erdos636_profile_count_ramseyFree (C * Real.log 2)
      (mul_pos hC hlogTwo) with ⟨γ, hγ, N, hN⟩
  refine ⟨γ, hγ, N, ?_⟩
  intro n hn G hG
  exact hN n hn G ((Erdos88.homogeneousFree_iff_ramseyFree C G).mp hG)

/-- The product scale used by the finite assembly is exactly the real-power
scale `n^(5/2)`. -/
lemma natCast_sq_mul_sqrt_eq_rpow_five_halves (n : ℕ) :
    (n : ℝ) ^ 2 * Real.sqrt n = (n : ℝ) ^ (5 / 2 : ℝ) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  by_cases hn0 : (n : ℝ) = 0
  · simp [hn0]
  · have hnpos : 0 < (n : ℝ) := lt_of_le_of_ne hn (Ne.symm hn0)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_add hnpos]
    congr 1
    norm_num

/-- Literal `n^(5/2)` form of the profile-count theorem. -/
theorem erdos636_profile_count_rpow (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        γ * (n : ℝ) ^ (5 / 2 : ℝ) ≤ (inducedProfiles G).card := by
  rcases erdos636_profile_count C hC with ⟨γ, hγ, N, hN⟩
  refine ⟨γ, hγ, N, ?_⟩
  intro n hn G hG
  rw [← natCast_sq_mul_sqrt_eq_rpow_five_halves]
  simpa only [mul_assoc] using hN n hn G hG

/-- **Resolution of Erdős Problem 636 (Kwan--Sudakov).**

For every positive `C`, all sufficiently large graphs on `n` vertices with
no clique or independent set of size at least `C * log n` contain a family
of at least `gamma * n^2 * sqrt n` induced vertex sets whose profiles are
pairwise distinct.  Injectivity of `inducedProfile` says literally that two
different members differ in their number of vertices or their number of
induced edges. -/
theorem erdos_636 (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        ∃ F : Finset (Finset (Fin n)),
          IsProfileInjectiveFamily G F ∧
            γ * (n : ℝ) ^ 2 * Real.sqrt n ≤ (F.card : ℝ) := by
  rcases erdos636_profile_count C hC with ⟨γ, hγ, N, hN⟩
  refine ⟨γ, hγ, N, ?_⟩
  intro n hn G hG
  obtain ⟨F, hF, hcard⟩ := exists_profileInjectiveFamily_card_eq_profiles G
  refine ⟨F, hF, ?_⟩
  rw [hcard]
  exact hN n hn G hG

/-- Literal `n^(5/2)` form of the pairwise profile-distinct family theorem. -/
theorem erdos636_rpow (C : ℝ) (hC : 0 < C) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ G : SimpleGraph (Fin n), Erdos88.HomogeneousFree C G →
        ∃ F : Finset (Finset (Fin n)),
          IsProfileInjectiveFamily G F ∧
            γ * (n : ℝ) ^ (5 / 2 : ℝ) ≤ (F.card : ℝ) := by
  rcases erdos_636 C hC with ⟨γ, hγ, N, hN⟩
  refine ⟨γ, hγ, N, ?_⟩
  intro n hn G hG
  obtain ⟨F, hF, hcard⟩ := hN n hn G hG
  refine ⟨F, hF, ?_⟩
  rw [← natCast_sq_mul_sqrt_eq_rpow_five_halves]
  simpa only [mul_assoc] using hcard

end Erdos636

alias _root_.Erdos636.erdos636 := _root_.Erdos636.erdos_636
