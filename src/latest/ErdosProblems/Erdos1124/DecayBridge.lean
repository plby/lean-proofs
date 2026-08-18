/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.FlowLimit
import ErdosProblems.Erdos1124.TorusAction

/-!
# From set discrepancy to a bounded flow

This file is the interface between the discrepancy statements for subsets of
the unit torus and the abstract limiting-flow construction.  If two sets have
the same volume and each of their dyadic orbit-cube densities approaches its
volume at rate `K * n ^ (-1 - δ)`, then the dyadic cube averages of their
signed indicator approach zero at the same rate, with constant `2 * K`.

The final theorems package the corresponding consequences from
`FlowLimit.lean`: absolute summability, a uniform geometric bound, and the
exact divergence equation.
-/

open scoped BigOperators
open MeasureTheory

namespace Erdos1124.DecayBridge

noncomputable section

open TorusAction

/-- A decay estimate which starts only after `q₀` can be promoted to a
uniform estimate by enlarging its constant.  The finitely many earlier scales
only need a common bound `M`.

The proof uses the explicit constant
`K + ∑ q < q₀, M * (2^q)^(1+δ)`.  Thus it is useful even when the
asymptotic argument naturally discards a finite initial range. -/
theorem exists_uniformDyadicDecay_of_eventually
    {d : ℕ} {X : Type*} [AddAction (Flow.Lattice d) X]
    (f : X → ℝ) (q₀ : ℕ) (K M δ : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (heventual : ∀ (q : ℕ), q₀ ≤ q → ∀ x : X,
      |Flow.cubeAverage (d := d) f (2 ^ q) x| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hinitial : ∀ (q : ℕ), q < q₀ → ∀ x : X,
      |Flow.cubeAverage (d := d) f (2 ^ q) x| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ Flow.UniformDyadicDecay (d := d) f C δ := by
  let C : ℝ := K + (∑ q ∈ Finset.range q₀,
    M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)))
  have hterm_nonneg : ∀ q : ℕ,
      0 ≤ M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) := by
    intro q
    exact mul_nonneg hM (Real.rpow_nonneg (by positivity) _)
  have hsum_nonneg : 0 ≤ ∑ q ∈ Finset.range q₀,
      M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) :=
    Finset.sum_nonneg fun q _ ↦ hterm_nonneg q
  have hC_nonneg : 0 ≤ C := add_nonneg hK hsum_nonneg
  refine ⟨C, hC_nonneg, hC_nonneg, hδ, ?_⟩
  intro q x
  by_cases hq : q₀ ≤ q
  · refine (heventual q hq x).trans ?_
    exact mul_le_mul_of_nonneg_right
      (show K ≤ C by exact le_add_of_nonneg_right hsum_nonneg)
      (Real.rpow_nonneg (by positivity) _)
  · have hq' : q < q₀ := Nat.lt_of_not_ge hq
    have hmem : q ∈ Finset.range q₀ := Finset.mem_range.mpr hq'
    have hterm_le_sum :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤
          ∑ r ∈ Finset.range q₀,
            M * ((((2 ^ r : ℕ) : ℝ)) ^ (1 + δ)) := by
      exact Finset.single_le_sum (fun r _ ↦ hterm_nonneg r) hmem
    have hterm_le_C :
        M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ)) ≤ C :=
      hterm_le_sum.trans (le_add_of_nonneg_left hK)
    have hmul := mul_le_mul_of_nonneg_right hterm_le_C
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ ((2 ^ q : ℕ) : ℝ)) (-1 - δ))
    refine (hinitial q hq' x).trans ?_
    calc
      M = (M * ((((2 ^ q : ℕ) : ℝ)) ^ (1 + δ))) *
          ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
        rw [mul_assoc, ← Real.rpow_add (by positivity :
          (0 : ℝ) < ((2 ^ q : ℕ) : ℝ))]
        have hexp : (1 + δ) + (-1 - δ) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
      _ ≤ C * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := hmul

/-- A uniform discrepancy estimate for one set along every dyadic orbit cube.

The positivity assumptions on `K` and `δ` are kept separate.  This makes the
predicate exactly match the quantitative estimates produced by the analytic
part of the proof. -/
def UniformSetDyadicDiscrepancy {d k : ℕ}
    (u : Fin d → Torus k) (E : Set (Torus k)) (K δ : ℝ) : Prop :=
  ∀ (q : ℕ) (x : Torus k),
    discrepancy u E (2 ^ q) x ≤
      K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))

/-- Equal-volume dyadic discrepancy for two sets gives uniform dyadic decay
of their signed indicator.  This version records the exact equality needed by
the proof, namely equality of the real values of the two volumes. -/
theorem uniformDyadicDecay_signedIndicator_of_volume_toReal_eq
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ) :
    letI := torusAddAction u
    Flow.UniformDyadicDecay (d := d) (signedIndicator A B) (2 * K) δ := by
  letI := torusAddAction u
  refine ⟨by positivity, hδ, ?_⟩
  intro q x
  have hA' :
      |cubeDensity u A (2 ^ q) x - (volume A).toReal| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
    exact hA q x
  have hB' :
      |cubeDensity u B (2 ^ q) x - (volume A).toReal| ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
    rw [hvolume]
    exact hB q x
  calc
    |Flow.cubeAverage (d := d) (signedIndicator A B) (2 ^ q) x| ≤
        2 * (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :=
      abs_cubeAverage_signedIndicator_le u A B (2 ^ q) x
        (volume A).toReal
        (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) hA' hB'
    _ = (2 * K) * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by ring

/-- The same bridge with equality in `ℝ≥0∞`, which is the form naturally
produced by geometric volume computations. -/
theorem uniformDyadicDecay_signedIndicator_of_volume_eq
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : volume A = volume B)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ) :
    letI := torusAddAction u
    Flow.UniformDyadicDecay (d := d) (signedIndicator A B) (2 * K) δ := by
  apply uniformDyadicDecay_signedIndicator_of_volume_toReal_eq
    u A B K δ hK hδ (congrArg ENNReal.toReal hvolume) hA hB

/-- Eventual set discrepancy is enough: the finitely many omitted signed
cube averages may be controlled by any common bound `M` (in applications one
can simply use `1` or `2`).  The conclusion supplies a new uniform constant,
so all of `FlowLimit.lean` becomes available without changing the exponent.
-/
theorem exists_uniformDyadicDecay_signedIndicator_of_eventual_discrepancy
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k))
    (q₀ : ℕ) (K M δ : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : ∀ (q : ℕ), q₀ ≤ q → ∀ x : Torus k,
      discrepancy u A (2 ^ q) x ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hB : ∀ (q : ℕ), q₀ ≤ q → ∀ x : Torus k,
      discrepancy u B (2 ^ q) x ≤
        K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)))
    (hinitial : ∀ (q : ℕ), q < q₀ → ∀ x : Torus k,
      letI := torusAddAction u
      |Flow.cubeAverage (d := d) (signedIndicator A B) (2 ^ q) x| ≤ M) :
    letI := torusAddAction u
    ∃ C : ℝ, 0 ≤ C ∧
      Flow.UniformDyadicDecay (d := d) (signedIndicator A B) C δ := by
  letI := torusAddAction u
  apply exists_uniformDyadicDecay_of_eventually
    (d := d) (signedIndicator A B) q₀ (2 * K) M δ (by positivity) hM hδ
  · intro q hq x
    have hA' :
        |cubeDensity u A (2 ^ q) x - (volume A).toReal| ≤
          K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := hA q hq x
    have hB' :
        |cubeDensity u B (2 ^ q) x - (volume A).toReal| ≤
          K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by
      rw [hvolume]
      exact hB q hq x
    calc
      |Flow.cubeAverage (d := d) (signedIndicator A B) (2 ^ q) x| ≤
          2 * (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) :=
        abs_cubeAverage_signedIndicator_le u A B (2 ^ q) x
          (volume A).toReal
          (K * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ))) hA' hB'
      _ = (2 * K) * ((((2 ^ q : ℕ) : ℝ)) ^ (-1 - δ)) := by ring
  · exact hinitial

/-- Under equal-volume discrepancy, every directed-edge scale series for the
signed indicator is absolutely summable. -/
theorem summable_scaleFlow_signedIndicator
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ)
    (g : Flow.BitDirection d) (x : Torus k) :
    letI := torusAddAction u
    Summable (fun q : ℕ ↦
      Flow.scaleFlow (d := d) (signedIndicator A B) (2 ^ q) g x) := by
  letI := torusAddAction u
  exact Flow.summable_scaleFlow_dyadic (signedIndicator A B) (2 * K) δ
    (uniformDyadicDecay_signedIndicator_of_volume_toReal_eq
      u A B K δ hK hδ hvolume hA hB) g x

/-- The limiting real flow associated to the two sets has a uniform geometric
bound on every directed edge. -/
theorem abs_dyadicFlow_signedIndicator_le
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ)
    (g : Flow.BitDirection d) (x : Torus k) :
    letI := torusAddAction u
    |Flow.dyadicFlow (d := d) (signedIndicator A B) g x| ≤
      Flow.geometricFlowBound (2 * K) δ := by
  letI := torusAddAction u
  exact Flow.abs_dyadicFlow_le_geometricFlowBound
    (signedIndicator A B) (2 * K) δ
    (uniformDyadicDecay_signedIndicator_of_volume_toReal_eq
      u A B K δ hK hδ hvolume hA hB) g x

/-- The limiting real flow solves the exact source-minus-target divergence
equation. -/
theorem divergence_dyadicFlow_signedIndicator
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ) (x : Torus k) :
    letI := torusAddAction u
    Flow.divergence (d := d)
        (Flow.dyadicFlow (d := d) (signedIndicator A B)) x =
      -signedIndicator A B x := by
  letI := torusAddAction u
  exact Flow.divergence_dyadicFlow_eq_neg
    (signedIndicator A B) (2 * K) δ
    (uniformDyadicDecay_signedIndicator_of_volume_toReal_eq
      u A B K δ hK hδ hvolume hA hB) x

/-- A single application-facing package: there exists a uniformly bounded
real flow whose divergence is target demand minus source demand. -/
theorem exists_bounded_flow_of_equal_volume_discrepancy
    {d k : ℕ} (u : Fin d → Torus k) (A B : Set (Torus k)) (K δ : ℝ)
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (hvolume : (volume A).toReal = (volume B).toReal)
    (hA : UniformSetDyadicDiscrepancy u A K δ)
    (hB : UniformSetDyadicDiscrepancy u B K δ) :
    letI := torusAddAction u
    ∃ φ : Flow.DirectionalFlow (d := d) (X := Torus k) (𝕜 := ℝ),
      (∀ g x, |φ g x| ≤ Flow.geometricFlowBound (2 * K) δ) ∧
      ∀ x, Flow.divergence (d := d) φ x = -signedIndicator A B x := by
  letI := torusAddAction u
  refine ⟨Flow.dyadicFlow (d := d) (signedIndicator A B), ?_, ?_⟩
  · exact fun g x ↦ abs_dyadicFlow_signedIndicator_le
      u A B K δ hK hδ hvolume hA hB g x
  · exact fun x ↦ divergence_dyadicFlow_signedIndicator
      u A B K δ hK hδ hvolume hA hB x

end

end Erdos1124.DecayBridge
