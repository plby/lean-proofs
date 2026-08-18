/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.BitGraph
import ErdosProblems.Erdos1124.DecayBridge
import ErdosProblems.Erdos1124.OrbitBlockCounts
import ErdosProblems.Erdos1124.OrbitBitBounds
import ErdosProblems.Erdos1124.OrbitBlocks
import ErdosProblems.Erdos1124.RoomBounds

/-!
# The abstract Laczkovich implication on a torus

This file assembles the analytic and combinatorial parts of the circle-squaring
argument.  Uniform dyadic discrepancy first gives a bounded real flow, which
is rounded to a bounded integer flow without changing its divergence.  The
integer flow is then ready for the finite-block matching theorem.

The final geometric estimates for the canonical orbit blocks are kept in
separate files; the intermediate theorem in this file deliberately exposes
their four conclusions (degree, cut capacity, room, and bounded displacement).
-/

open Set MeasureTheory

namespace Erdos1124.TorusLaczkovich

noncomputable section

open TorusAction

/-- Uniform dyadic density error about a prescribed real mean.  Unlike
`UniformSetDyadicDiscrepancy`, this predicate does not mention the measure of
the set; it is the interface naturally supplied by the concrete grid count. -/
def UniformMeanDyadicDensity {d k : ℕ}
    (u : Fin d → Torus k) (E : Set (Torus k))
    (μ K δ : ℝ) : Prop :=
  ∀ (q : ℕ) (x : Torus k),
    |cubeDensity u E (2 ^ q) x - μ| ≤
      K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))

/-- Injectivity of torus displacement is the pointwise freeness required by
the canonical orbit-block construction. -/
lemma torusFreeAction_of_free {d k : ℕ} (u : Fin d → Torus k)
    (hu : Free u) :
    letI := torusAddAction u
    OrbitBlocks.FreeAction (d := d) (X := Torus k) := by
  letI := torusAddAction u
  intro x m n hmn
  apply hu
  exact add_right_cancel hmn

/-- The closed-form geometric-series bound used for the real flow is
nonnegative under the discrepancy hypotheses. -/
lemma geometricFlowBound_nonneg {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    0 ≤ Flow.geometricFlowBound C δ := by
  have hr : (2 : ℝ) ^ (-δ) < 1 := Flow.dyadicRatio_lt_one hδ
  exact mul_nonneg hC (inv_nonneg.mpr (sub_nonneg.mpr hr.le))

/-- An indexed orbit cube contains at most one unit of indicator mass per
index.  This estimate does not require freeness. -/
lemma cubeCount_le_pow {d k n : ℕ} (u : Fin d → Torus k)
    (E : Set (Torus k)) (x : Torus k) :
    cubeCount u E n x ≤ n ^ d := by
  classical
  letI := torusAddAction u
  unfold cubeCount
  calc
    (∑ q : Fin d → Fin n, if (-Flow.cubeIndex q +ᵥ x) ∈ E then 1 else 0) ≤
        ∑ _q : Fin d → Fin n, 1 := by
          apply Finset.sum_le_sum
          intro q hq
          split_ifs <;> omega
    _ = n ^ d := by simp

/-- Every positive-side normalized orbit count lies in the unit interval. -/
lemma cubeDensity_mem_Icc {d k n : ℕ} (u : Fin d → Torus k)
    (E : Set (Torus k)) (x : Torus k) (hn : 0 < n) :
    cubeDensity u E n x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · unfold cubeDensity
    rw [div_le_one (by positivity : (0 : ℝ) < (n : ℝ) ^ d)]
    exact_mod_cast cubeCount_le_pow u E x

/-- A crude bound for the finitely many density estimates before an
asymptotic estimate starts. -/
lemma abs_cubeDensity_sub_mean_le {d k n : ℕ} (u : Fin d → Torus k)
    (E : Set (Torus k)) (x : Torus k) (μ : ℝ) (hn : 0 < n) :
    |cubeDensity u E n x - μ| ≤ 1 + |μ| := by
  rcases cubeDensity_mem_Icc u E x hn with ⟨h0, h1⟩
  calc
    |cubeDensity u E n x - μ| ≤ |cubeDensity u E n x| + |μ| := abs_sub _ _
    _ = cubeDensity u E n x + |μ| := by rw [abs_of_nonneg h0]
    _ ≤ 1 + |μ| := by linarith

/-- Promote an eventual common-mean density estimate to a uniform one by
enlarging its constant over the finite initial range. -/
theorem exists_uniformMeanDyadicDensity_of_eventually
    {d k : ℕ} (u : Fin d → Torus k) (E : Set (Torus k))
    (μ : ℝ) (q₀ : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (heventual : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u E (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :
    ∃ C : ℝ, 0 ≤ C ∧ UniformMeanDyadicDensity u E μ C δ := by
  let M : ℝ := 1 + |μ|
  let C : ℝ := K + (∑ q ∈ Finset.range q₀,
    M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)))
  have hM : 0 ≤ M := by positivity
  have hterm : ∀ q : ℕ,
      0 ≤ M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) := by
    intro q
    exact mul_nonneg hM (Real.rpow_nonneg (by positivity) _)
  have hsum : 0 ≤ ∑ q ∈ Finset.range q₀,
      M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) :=
    Finset.sum_nonneg fun q _ ↦ hterm q
  have hC : 0 ≤ C := add_nonneg hK hsum
  refine ⟨C, hC, ?_⟩
  intro q x
  by_cases hq : q₀ ≤ q
  · exact (heventual q hq x).trans (mul_le_mul_of_nonneg_right
      (show K ≤ C by exact le_add_of_nonneg_right hsum)
      (Real.rpow_nonneg (by positivity) _))
  · have hq' : q < q₀ := Nat.lt_of_not_ge hq
    have hmem : q ∈ Finset.range q₀ := Finset.mem_range.mpr hq'
    have hterm_le_sum :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤
          ∑ r ∈ Finset.range q₀,
            M * ((((2 ^ r : ℕ) : ℝ)) ^ (1 + δ)) :=
      Finset.single_le_sum (fun r _ ↦ hterm r) hmem
    have hterm_le_C :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤ C :=
      hterm_le_sum.trans (le_add_of_nonneg_left hK)
    refine (abs_cubeDensity_sub_mean_le u E x μ (by positivity)).trans ?_
    calc
      M = (M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ))) *
          ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity :
          (0 : ℝ) < ((2 ^ q : ℕ) : ℝ))]
        have hexp : (1 + δ) + (-1 - δ) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
      _ ≤ C * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) :=
        mul_le_mul_of_nonneg_right hterm_le_C
          (Real.rpow_nonneg (by positivity) _)

/-- A single enlarged constant works for two eventual density estimates. -/
theorem exists_uniformMeanDyadicDensity_pair_of_eventually
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (μ : ℝ) (q₀ : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u A (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hB : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u B (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      UniformMeanDyadicDensity u A μ C δ ∧
      UniformMeanDyadicDensity u B μ C δ := by
  obtain ⟨CA, hCA, hAu⟩ :=
    exists_uniformMeanDyadicDensity_of_eventually
      u A μ q₀ K δ hK hδ hA
  obtain ⟨CB, hCB, hBu⟩ :=
    exists_uniformMeanDyadicDensity_of_eventually
      u B μ q₀ K δ hK hδ hB
  refine ⟨CA + CB, add_nonneg hCA hCB, ?_, ?_⟩
  · intro q x
    exact (hAu q x).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hCB) (Real.rpow_nonneg (by positivity) _))
  · intro q x
    exact (hBu q x).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left hCA) (Real.rpow_nonneg (by positivity) _))

/-- The finitely many initial signed cube averages omitted by an eventual
discrepancy estimate have the universal bound one. -/
lemma abs_cubeAverage_signedIndicator_le_one
    {d k n : ℕ} (u : Fin d → Torus k)
    (A B : Set (Torus k)) (x : Torus k) (hn : 0 < n) :
    letI := torusAddAction u
    |Flow.cubeAverage (d := d) (signedIndicator A B) n x| ≤ 1 := by
  letI := torusAddAction u
  rw [cubeAverage_signedIndicator]
  rcases cubeDensity_mem_Icc u A x hn with ⟨hA0, hA1⟩
  rcases cubeDensity_mem_Icc u B x hn with ⟨hB0, hB1⟩
  rw [abs_le]
  constructor <;> linarith

/-- Two density estimates around the same prescribed mean give the dyadic
decay needed by the flow construction, independently of any measure
identification for the sets. -/
theorem uniformDyadicDecay_signedIndicator_of_commonMean
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (μ K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : UniformMeanDyadicDensity u A μ K δ)
    (hB : UniformMeanDyadicDensity u B μ K δ) :
    letI := torusAddAction u
    Flow.UniformDyadicDecay (d := d) (signedIndicator A B) (2 * K) δ := by
  letI := torusAddAction u
  refine ⟨by positivity, hδ, ?_⟩
  intro q x
  calc
    |Flow.cubeAverage (d := d) (signedIndicator A B) (2 ^ q) x| ≤
        2 * (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :=
      abs_cubeAverage_signedIndicator_le u A B (2 ^ q) x μ
        (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) (hA q x) (hB q x)
    _ = (2 * K) * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by ring

/-- Common-mean dyadic estimates yield a bounded integral bit flow, without
first identifying the common mean with Haar measure. -/
theorem exists_integral_bitFlow_of_commonMeanDyadicDensity
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (μ K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : UniformMeanDyadicDensity u A μ K δ)
    (hB : UniformMeanDyadicDensity u B μ K δ) :
    let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
    ∃ ψ : Torus k → Flow.BitDirection d → ℤ,
      (∀ x g, |ψ x g| ≤ b) ∧
      ∀ x, (BitGraph.bitPermutationGraph u).divergence ψ x =
        BitGraph.intDemand A B x := by
  let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
  letI := torusAddAction u
  have hdecay := uniformDyadicDecay_signedIndicator_of_commonMean
    u A B μ K δ hK hδ hA hB
  let φ := Flow.dyadicFlow (d := d) (signedIndicator A B)
  apply BitGraph.exists_integral_bitFlow u A B φ b
  · intro x
    exact Flow.divergence_dyadicFlow_eq_neg
      (signedIndicator A B) (2 * K) δ hdecay x
  · intro g x
    exact (Flow.abs_dyadicFlow_le_geometricFlowBound
      (signedIndicator A B) (2 * K) δ hdecay g x).trans (Nat.le_ceil _)

/-- Eventual common-mean estimates suffice for the integral-flow step.  The
finite prefix uses the universal unit bound on signed cube averages. -/
theorem exists_integral_bitFlow_of_eventualCommonMeanDensity
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (μ : ℝ) (q₀ : ℕ) (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u A (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hB : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u B (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      let b := ⌈Flow.geometricFlowBound C δ⌉₊
      ∃ ψ : Torus k → Flow.BitDirection d → ℤ,
        (∀ x g, |ψ x g| ≤ b) ∧
        ∀ x, (BitGraph.bitPermutationGraph u).divergence ψ x =
          BitGraph.intDemand A B x := by
  letI := torusAddAction u
  obtain ⟨C, hC, hdecay⟩ :=
    DecayBridge.exists_uniformDyadicDecay_of_eventually
      (d := d) (signedIndicator A B) q₀ (2 * K) 1 δ
      (by positivity) (by norm_num) hδ (by
        intro q hq x
        exact abs_cubeAverage_signedIndicator_le u A B (2 ^ q) x μ
          (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) (hA q hq x) (hB q hq x)
          |>.trans_eq (by ring)) (by
        intro q hq x
        exact abs_cubeAverage_signedIndicator_le_one u A B x (by positivity))
  refine ⟨C, hC, ?_⟩
  let φ := Flow.dyadicFlow (d := d) (signedIndicator A B)
  apply BitGraph.exists_integral_bitFlow u A B φ
    ⌈Flow.geometricFlowBound C δ⌉₊
  · intro x
    exact Flow.divergence_dyadicFlow_eq_neg
      (signedIndicator A B) C δ hdecay x
  · intro g x
    exact (Flow.abs_dyadicFlow_le_geometricFlowBound
      (signedIndicator A B) C δ hdecay g x).trans (Nat.le_ceil _)

/-- Uniform dyadic discrepancy yields an integer-valued bit-direction flow.
Its capacity is the natural ceiling of the geometric-series bound. -/
theorem exists_integral_bitFlow_of_uniformDyadicDiscrepancy
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : DecayBridge.UniformSetDyadicDiscrepancy u A K δ)
    (hB : DecayBridge.UniformSetDyadicDiscrepancy u B K δ) :
    let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
    ∃ ψ : Torus k → Flow.BitDirection d → ℤ,
      (∀ x g, |ψ x g| ≤ b) ∧
      ∀ x, (BitGraph.bitPermutationGraph u).divergence ψ x =
        BitGraph.intDemand A B x := by
  let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
  letI := torusAddAction u
  obtain ⟨φ, hφbound, hφdiv⟩ :=
    DecayBridge.exists_bounded_flow_of_equal_volume_discrepancy
      u A B K δ hK hδ hvolume hA hB
  apply BitGraph.exists_integral_bitFlow u A B φ b hφdiv
  intro g x
  exact (hφbound g x).trans (Nat.le_ceil _)

/-- Eventual dyadic discrepancy also gives a bounded integer flow.  The
finite initial range is absorbed using
`abs_cubeAverage_signedIndicator_le_one`. -/
theorem exists_integral_bitFlow_of_eventualDyadicDiscrepancy
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (q₀ : ℕ) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : ∀ q, q₀ ≤ q → ∀ x,
      discrepancy u A (2 ^ q) x ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hB : ∀ q, q₀ ≤ q → ∀ x,
      discrepancy u B (2 ^ q) x ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :
    ∃ C : ℝ, 0 ≤ C ∧
      let b := ⌈Flow.geometricFlowBound C δ⌉₊
      ∃ ψ : Torus k → Flow.BitDirection d → ℤ,
        (∀ x g, |ψ x g| ≤ b) ∧
        ∀ x, (BitGraph.bitPermutationGraph u).divergence ψ x =
          BitGraph.intDemand A B x := by
  letI := torusAddAction u
  obtain ⟨C, hC, hdecay⟩ :=
    DecayBridge.exists_uniformDyadicDecay_signedIndicator_of_eventual_discrepancy
      u A B q₀ K 1 δ hK (by norm_num) hδ hvolume hA hB (by
        intro q hq x
        exact abs_cubeAverage_signedIndicator_le_one u A B x (by positivity))
  refine ⟨C, hC, ?_⟩
  let φ := Flow.dyadicFlow (d := d) (signedIndicator A B)
  apply BitGraph.exists_integral_bitFlow u A B φ
    ⌈Flow.geometricFlowBound C δ⌉₊
  · intro x
    exact Flow.divergence_dyadicFlow_eq_neg
      (signedIndicator A B) C δ hdecay x
  · intro g x
    exact (Flow.abs_dyadicFlow_le_geometricFlowBound
      (signedIndicator A B) C δ hdecay g x).trans (Nat.le_ceil _)

/-- Choose a dyadic block scale at which both sets have enough points to pay
for every diagonal-bit boundary flow.  The constants are the canonical coarse
bounds: at most `3^d` neighboring blocks and at most
`2^(d+1) * b * M^(d-1)` units on one net block edge. -/
theorem exists_dyadic_room_for_integral_bitFlow
    {d k : ℕ} (u : Fin d → Torus k) (hu : Free u)
    (A B : Set (Torus k)) (K δ : ℝ)
    (hd : 0 < d) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hvolume_pos : 0 < (volume A).toReal)
    (hA : DecayBridge.UniformSetDyadicDiscrepancy u A K δ)
    (hB : DecayBridge.UniformSetDyadicDiscrepancy u B K δ) :
    let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
    ∃ q : ℕ, let M : ℕ := 2 ^ q
      letI : NeZero M := inferInstance
      letI := torusAddAction u
      (∀ i : OrbitBlocks.BlockIndex (d := d) (X := Torus k),
        3 ^ d * ((2 ^ (d + 1) * b) * M ^ (d - 1)) ≤
          (OrbitBlocks.pointsInBlock (d := d) A M i).card) ∧
      (∀ i : OrbitBlocks.BlockIndex (d := d) (X := Torus k),
        3 ^ d * ((2 ^ (d + 1) * b) * M ^ (d - 1)) ≤
          (OrbitBlocks.pointsInBlock (d := d) B M i).card) := by
  let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
  apply OrbitBlockCounts.exists_dyadic_uniform_room_pair_of_discrepancy
    u hu A B (volume A).toReal K δ (3 ^ d) (2 ^ (d + 1) * b)
    hd hvolume_pos hK hδ.le
  · intro q x
    simpa only [DecayBridge.UniformSetDyadicDiscrepancy,
      show -(1 + δ) = -1 - δ by ring] using hA q x
  · intro q x
    simpa only [DecayBridge.UniformSetDyadicDiscrepancy,
      show -(1 + δ) = -1 - δ by ring] using hB q x
  · rfl
  · exact hvolume.symm

/-- The direct common-mean version of the dyadic room selection.  This is
the form used by the concrete disk and square grid estimates. -/
theorem exists_dyadic_room_for_commonMeanDensity
    {d k : ℕ} (u : Fin d → Torus k) (hu : Free u)
    (A B : Set (Torus k)) (μ K δ : ℝ)
    (hd : 0 < d) (hμ : 0 < μ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : UniformMeanDyadicDensity u A μ K δ)
    (hB : UniformMeanDyadicDensity u B μ K δ) :
    let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
    ∃ q : ℕ, let M : ℕ := 2 ^ q
      letI : NeZero M := inferInstance
      letI := torusAddAction u
      (∀ i : OrbitBlocks.BlockIndex (d := d) (X := Torus k),
        3 ^ d * ((2 ^ (d + 1) * b) * M ^ (d - 1)) ≤
          (OrbitBlocks.pointsInBlock (d := d) A M i).card) ∧
      (∀ i : OrbitBlocks.BlockIndex (d := d) (X := Torus k),
        3 ^ d * ((2 ^ (d + 1) * b) * M ^ (d - 1)) ≤
          (OrbitBlocks.pointsInBlock (d := d) B M i).card) := by
  let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
  apply OrbitBlockCounts.exists_dyadic_uniform_room_pair
    u hu A B μ K δ (3 ^ d) (2 ^ (d + 1) * b)
    hd hμ hK hδ.le
  · intro q x
    simpa only [show -(1 + δ) = -1 - δ by ring] using hA q x
  · intro q x
    simpa only [show -(1 + δ) = -1 - δ by ring] using hB q x

/-- The graph divergence of a bit flow is exactly the orbit-block divergence
after transposing the two curried arguments. -/
lemma bitDivergence_eq_bitGraph_divergence
    {d k : ℕ} (u : Fin d → Torus k)
    (ψ : Torus k → Flow.BitDirection d → ℤ) (x : Torus k) :
    letI := torusAddAction u
    OrbitBlocks.bitDivergence (d := d) (fun g x ↦ ψ x g) x =
      (BitGraph.bitPermutationGraph u).divergence ψ x := by
  letI := torusAddAction u
  unfold OrbitBlocks.bitDivergence IntegralFlow.PermutationGraph.divergence
  apply Finset.sum_congr rfl
  intro g hg
  rw [BitGraph.bitPermutationGraph_move_symm_apply]
  rfl

/-- Abstract final block step.  This theorem fixes all convention changes
between discrepancy, real flow, integral flow, and block matching.  Its
remaining hypotheses are precisely the canonical-block estimates proved by
the orbit-bound modules. -/
theorem exists_equidecomp_of_uniformDyadicDiscrepancy_of_block_bounds
    {d k : ℕ} (u : Fin d → Torus k)
    (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : DecayBridge.UniformSetDyadicDiscrepancy u A K δ)
    (hB : DecayBridge.UniformSetDyadicDiscrepancy u B K δ) :
    letI := torusAddAction u
    ∀ (hu : OrbitBlocks.FreeAction (d := d) (X := Torus k))
      (M degree capacity : ℕ) [NeZero M]
      (D : Finset (Torus k)),
      (∀ i, (OrbitBlocks.orbitAdjacentBlocks hu M i).card ≤ degree) →
      (∀ (ψ : Torus k → Flow.BitDirection d → ℤ),
        (∀ x g, |ψ x g| ≤ ⌈Flow.geometricFlowBound (2 * K) δ⌉₊) →
        ∀ i j,
          OrbitBlocks.orbitNetBlockFlow hu M (fun g x ↦ ψ x g) i j ≤ capacity) →
      (∀ i, degree * capacity ≤
        (OrbitBlocks.pointsInBlock (d := d) A M i).card) →
      (∀ i, degree * capacity ≤
        (OrbitBlocks.pointsInBlock (d := d) B M i).card) →
      (∀ (a : A) (b : B),
        OrbitBlocks.blockOf (d := d) M (b : Torus k) =
            OrbitBlocks.blockOf (d := d) M (a : Torus k) ∨
          OrbitBlocks.blockOf (d := d) M (b : Torus k) ∈
            OrbitBlocks.orbitAdjacentBlocks hu M
              (OrbitBlocks.blockOf (d := d) M (a : Torus k)) →
        (b : Torus k) - (a : Torus k) ∈ D) →
      ∃ e : Equidecomp (Torus k) (Multiplicative (Torus k)),
        e.source = A ∧ e.target = B ∧
          Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  letI := torusAddAction u
  intro hu M degree capacity hM D hdegree hcapacity hroomA hroomB hallowed
  obtain ⟨ψ, hψbound, hψdiv⟩ :=
    exists_integral_bitFlow_of_uniformDyadicDiscrepancy
      u A B K δ hK hδ hvolume hA hB
  apply OrbitBlocks.exists_equidecomp_of_orbitBitFlow
    hu A B D M degree capacity (fun g x ↦ ψ x g)
  · exact hdegree
  · exact hcapacity ψ hψbound
  · intro x
    rw [bitDivergence_eq_bitGraph_divergence u ψ x, hψdiv x]
    rfl
  · exact hroomA
  · exact hroomB
  · exact hallowed

/-- Direct common-mean counterpart of the abstract final block step. -/
theorem exists_equidecomp_of_commonMeanDensity_of_block_bounds
    {d k : ℕ} (u : Fin d → Torus k)
    (A B : Set (Torus k)) (μ K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : UniformMeanDyadicDensity u A μ K δ)
    (hB : UniformMeanDyadicDensity u B μ K δ) :
    letI := torusAddAction u
    ∀ (hu : OrbitBlocks.FreeAction (d := d) (X := Torus k))
      (M degree capacity : ℕ) [NeZero M]
      (D : Finset (Torus k)),
      (∀ i, (OrbitBlocks.orbitAdjacentBlocks hu M i).card ≤ degree) →
      (∀ (ψ : Torus k → Flow.BitDirection d → ℤ),
        (∀ x g, |ψ x g| ≤ ⌈Flow.geometricFlowBound (2 * K) δ⌉₊) →
        ∀ i j,
          OrbitBlocks.orbitNetBlockFlow hu M (fun g x ↦ ψ x g) i j ≤ capacity) →
      (∀ i, degree * capacity ≤
        (OrbitBlocks.pointsInBlock (d := d) A M i).card) →
      (∀ i, degree * capacity ≤
        (OrbitBlocks.pointsInBlock (d := d) B M i).card) →
      (∀ (a : A) (b : B),
        OrbitBlocks.blockOf (d := d) M (b : Torus k) =
            OrbitBlocks.blockOf (d := d) M (a : Torus k) ∨
          OrbitBlocks.blockOf (d := d) M (b : Torus k) ∈
            OrbitBlocks.orbitAdjacentBlocks hu M
              (OrbitBlocks.blockOf (d := d) M (a : Torus k)) →
        (b : Torus k) - (a : Torus k) ∈ D) →
      ∃ e : Equidecomp (Torus k) (Multiplicative (Torus k)),
        e.source = A ∧ e.target = B ∧
          Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  letI := torusAddAction u
  intro hu M degree capacity hM D hdegree hcapacity hroomA hroomB hallowed
  obtain ⟨ψ, hψbound, hψdiv⟩ :=
    exists_integral_bitFlow_of_commonMeanDyadicDensity
      u A B μ K δ hK hδ hA hB
  apply OrbitBlocks.exists_equidecomp_of_orbitBitFlow
    hu A B D M degree capacity (fun g x ↦ ψ x g)
  · exact hdegree
  · exact hcapacity ψ hψbound
  · intro x
    rw [bitDivergence_eq_bitGraph_divergence u ψ x, hψdiv x]
    rfl
  · exact hroomA
  · exact hroomB
  · exact hallowed

/-- **Abstract Laczkovich theorem on a torus.**

For a free finitely generated torus action, positive common mean and uniform
dyadic density error of order `N⁻¹⁻δ` imply a finite translation
equidecomposition.  The finite set of translations is returned explicitly. -/
theorem exists_equidecomp_of_commonMeanDyadicDensity
    {d k : ℕ} (u : Fin d → Torus k) (hu : Free u)
    (A B : Set (Torus k)) (μ K δ : ℝ)
    (hd : 0 < d) (hμ : 0 < μ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : UniformMeanDyadicDensity u A μ K δ)
    (hB : UniformMeanDyadicDensity u B μ K δ) :
    ∃ (D : Finset (Torus k))
      (e : Equidecomp (Torus k) (Multiplicative (Torus k))),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  let b := ⌈Flow.geometricFlowBound (2 * K) δ⌉₊
  obtain ⟨q, hroomA, hroomB⟩ :=
    exists_dyadic_room_for_commonMeanDensity
      u hu A B μ K δ hd hμ hK hδ hA hB
  let M : ℕ := 2 ^ q
  letI : NeZero M := inferInstance
  obtain ⟨ψ, hψbound, hψdiv⟩ :=
    exists_integral_bitFlow_of_commonMeanDyadicDensity
      u A B μ K δ hK hδ hA hB
  refine ⟨OrbitBitBounds.orbitDisplacements
      (OrbitBitBounds.torusShift u) M, ?_⟩
  apply OrbitBitBounds.exists_equidecomp_of_torusBitFlow
    u hu A B M (fun g x ↦ ψ x g) b
  · exact fun g x ↦ hψbound x g
  · intro x
    rw [bitDivergence_eq_bitGraph_divergence u ψ x, hψdiv x]
    rfl
  · simpa only [M, b, mul_assoc] using hroomA
  · simpa only [M, b, mul_assoc] using hroomB

/-- Eventual dyadic common-mean estimates imply the same exact finite
translation equidecomposition.  The omitted finite prefix is absorbed into a
larger uniform constant. -/
theorem exists_equidecomp_of_eventualCommonMeanDyadicDensity
    {d k : ℕ} (u : Fin d → Torus k) (hu : Free u)
    (A B : Set (Torus k)) (μ : ℝ) (q₀ : ℕ) (K δ : ℝ)
    (hd : 0 < d) (hμ : 0 < μ) (hK : 0 ≤ K) (hδ : 0 < δ)
    (hA : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u A (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hB : ∀ q, q₀ ≤ q → ∀ x,
      |cubeDensity u B (2 ^ q) x - μ| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :
    ∃ (D : Finset (Torus k))
      (e : Equidecomp (Torus k) (Multiplicative (Torus k))),
      e.source = A ∧ e.target = B ∧
        Equidecomp.IsDecompOn e A (multiplicativeDisplacements D) := by
  obtain ⟨C, hC, hAu, hBu⟩ :=
    exists_uniformMeanDyadicDensity_pair_of_eventually
      u A B μ q₀ K δ hK hδ hA hB
  exact exists_equidecomp_of_commonMeanDyadicDensity
    u hu A B μ C δ hd hμ hC hδ hAu hBu

end

end Erdos1124.TorusLaczkovich
