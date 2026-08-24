/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1115.
https://www.erdosproblems.com/forum/thread/1115

Informal authors:
- A. A. Gol'dberg
- Alexandre Eremenko

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1115.md
-/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Tactic

/-!
# Erdős Problem 1115

Gol'dberg and Eremenko disproved the conjecture that every finite-order entire function admits an
asymptotic curve over infinity whose length in the disk of radius `r` is `O(r)`.  More sharply, an
arbitrarily slowly divergent factor multiplying Hayman's growth threshold `(log r)²` already
permits a counterexample.

The detailed mathematical reconstruction and the correspondence between the paper and this file
are in `tex/1115.tex`.
-/

open Filter MeasureTheory Set Topology unitInterval
open scoped ENNReal NNReal Topology

namespace Erdos1115

/-- The maximum modulus of `f` on the circle of radius `r`.  Only nonnegative radii are used. -/
noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The elementary growth formulation of finite order used in this development. -/
def EntireOfFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧
      ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ ρ)

/-- A curve represented with speed at most one.  Every locally rectifiable curve going to infinity
has such an arclength parametrization; allowing speed below one only increases the time (and hence
the arclength upper parameter) spent in a disk. -/
def IsArcLengthPath (γ : ℝ → ℂ) : Prop :=
  LipschitzWith 1 γ

/-- Both the curve and its image under `f` tend to infinity. -/
def EscapesAlong (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  Tendsto (fun t ↦ ‖γ t‖) atTop atTop ∧
    Tendsto (fun t ↦ ‖f (γ t)‖) atTop atTop

/-- Length in the open disk, for a speed-at-most-one arclength parameter.  Properness of an
escaping curve makes the displayed measure finite; `toReal` then recovers ordinary length. -/
noncomputable def lengthInDisc (γ : ℝ → ℂ) (r : ℝ) : ℝ :=
  ENNReal.toReal (volume {t | 0 ≤ t ∧ ‖γ t‖ < r})

/-- The assertion `ℓ(r) = O(r)` in the question. -/
def HasLinearLength (γ : ℝ → ℂ) : Prop :=
  (fun r : ℝ ↦ lengthInDisc γ r) =O[atTop] (fun r ↦ r)

/-- The near-Hayman growth estimate `log M(r,f) = O(φ(r) (log r)²)`, stated as the
one-sided estimate actually proved and used in the source. -/
def HasGolbergEremenkoGrowth (φ : ℝ → ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ᶠ r : ℝ in atTop,
      Real.log (maximumModulus f r) ≤ C * φ r * (Real.log r) ^ 2

/-- An asymptotic curve over infinity in the arclength model used by the theorem. -/
def IsAsymptoticPath (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  IsArcLengthPath γ ∧ EscapesAlong f γ

/-- A geometric wall whose eventual avoidance costs at least `cost` units of arclength before
leaving the disk of radius `outer`.  This definition contains no analytic information about `f`;
the spiral lemma below supplies it for the explicit walls. -/
def IsLengthBarrier (S : Set ℂ) (inner outer cost : ℝ) : Prop :=
  ∀ γ : ℝ → ℂ, IsArcLengthPath γ →
    Tendsto (fun t ↦ ‖γ t‖) atTop atTop →
    ∀ t₀ : ℝ, 0 ≤ t₀ → ‖γ t₀‖ < inner →
    (∀ t ≥ t₀, γ t ∉ S) →
    cost ≤ lengthInDisc γ outer

/-- The abstract certificate produced by the Gol'dberg--Eremenko construction: bounded-value
walls at radii tending to infinity, whose unavoidable length divided by radius tends to infinity. -/
def HasEscapingBarriers (f : ℂ → ℂ) : Prop :=
  ∃ (S : ℕ → Set ℂ) (inner outer cost : ℕ → ℝ),
    (∀ n, 0 < outer n) ∧
    Tendsto inner atTop atTop ∧
    Tendsto outer atTop atTop ∧
    Tendsto (fun n ↦ cost n / outer n) atTop atTop ∧
    ∀ n, (∀ z ∈ S n, ‖f z‖ ≤ 1) ∧
      IsLengthBarrier (S n) (inner n) (outer n) (cost n)

/-- The `k`-turn spiral used by Gol'dberg and Eremenko, dilated by `T`. -/
noncomputable def spiralPoint (k : ℕ) (T s : ℝ) : ℂ :=
  (T * s : ℂ) *
    Complex.exp (((2 * Real.pi * (k : ℝ) * (s - 2) : ℝ) : ℂ) * Complex.I)

/-- The image of the closed radial interval `[2,3]` under `spiralPoint`. -/
noncomputable def spiralSet (k : ℕ) (T : ℝ) : Set ℂ :=
  spiralPoint k T '' Set.Icc 2 3

lemma norm_spiralPoint (k : ℕ) {T s : ℝ} (hT : 0 ≤ T) (hs : 0 ≤ s) :
    ‖spiralPoint k T s‖ = T * s := by
  simp [spiralPoint, Complex.norm_exp, abs_of_nonneg hT,
    abs_of_nonneg hs]

lemma spiralSet_norm_bounds (k : ℕ) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ spiralSet k T) :
    2 * T ≤ ‖z‖ ∧ ‖z‖ ≤ 3 * T := by
  obtain ⟨s, hs, rfl⟩ := hz
  rw [norm_spiralPoint k hT (by linarith [hs.1])]
  constructor
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hs.1 hT
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left hs.2 hT

lemma isCompact_spiralSet (k : ℕ) (T : ℝ) : IsCompact (spiralSet k T) := by
  unfold spiralSet spiralPoint
  exact isCompact_Icc.image (by fun_prop)

/-- The uniform closure, on `K`, of restrictions of complex polynomials.  Encoding approximation
this way makes the algebra and limit closure needed in Runge's pole-moving argument automatic. -/
noncomputable def polynomialUniformClosure (K : Set ℂ) [CompactSpace K] : Subalgebra ℂ C(K, ℂ) :=
  (polynomialFunctions K).topologicalClosure

lemma polynomial_mem_uniformClosure (K : Set ℂ) [CompactSpace K] (p : Polynomial ℂ) :
    p.toContinuousMapOn K ∈ polynomialUniformClosure K := by
  apply Subalgebra.le_topologicalClosure
  change p.toContinuousMapOn K ∈ (polynomialFunctions K : Set C(K, ℂ))
  rw [polynomialFunctions_coe]
  exact ⟨p, rfl⟩

lemma exists_polynomial_near_of_mem_uniformClosure (K : Set ℂ) [CompactSpace K]
    (f : C(K, ℂ)) (hf : f ∈ polynomialUniformClosure K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ‖p.toContinuousMapOn K - f‖ < ε := by
  have hfreq := mem_closure_iff_frequently.mp hf
  rw [Metric.nhds_basis_ball.frequently_iff] at hfreq
  obtain ⟨-, hpdist, ⟨p, ⟨-, rfl⟩⟩⟩ := hfreq ε hε
  rw [Metric.mem_ball, dist_eq_norm] at hpdist
  exact ⟨p, hpdist⟩

/-- The resolvent kernel `z ↦ (z-a)⁻¹` restricted to a compact set avoiding its pole. -/
noncomputable def resolventOn (K : Set ℂ) (a : ℂ) (ha : a ∉ K) : C(K, ℂ) where
  toFun z := ((z : ℂ) - a)⁻¹
  continuous_toFun :=
    (continuous_subtype_val.sub continuous_const).inv₀ fun z hzero ↦
      ha (by
        have hz : (z : ℂ) = a := sub_eq_zero.mp hzero
        rw [← hz]
        exact z.property)

@[simp] lemma resolventOn_apply (K : Set ℂ) (a : ℂ) (ha : a ∉ K) (z : K) :
    resolventOn K a ha z = ((z : ℂ) - a)⁻¹ := rfl

/-- A closed subalgebra contains the sum of a convergent geometric series generated by one of its
elements.  Continuous maps do not have a global pointwise-inverse operation, so the sum is passed
explicitly rather than written as `(1 - x)⁻¹`. -/
lemma geometric_sum_mem_closedSubalgebra {B : Type*} [NormedRing B] [NormedAlgebra ℂ B]
    {A : Subalgebra ℂ B} (hA : IsClosed (A : Set B))
    {x y : B} (hx : x ∈ A) (hsum : HasSum (fun n : ℕ ↦ x ^ n) y) :
    y ∈ A := by
  apply hA.mem_of_tendsto hsum.tendsto_sum_nat
  filter_upwards [] with n
  exact A.sum_mem fun i _ ↦ A.pow_mem hx i

/-- A resolvent already in the polynomial closure can have its pole moved by a perturbation small
relative to its uniform norm. -/
lemma resolvent_mem_of_nearby {K : Set ℂ} [CompactSpace K] {a b : ℂ}
    (ha : a ∉ K) (hb : b ∉ K)
    (hgood : resolventOn K a ha ∈ polynomialUniformClosure K)
    (hnear : ‖(b - a) • resolventOn K a ha‖ < 1) :
    resolventOn K b hb ∈ polynomialUniformClosure K := by
  let A : Subalgebra ℂ C(K, ℂ) := polynomialUniformClosure K
  let x : C(K, ℂ) := (b - a) • resolventOn K a ha
  let y : C(K, ℂ) := ∑' n : ℕ, x ^ n
  have hx : x ∈ A := by
    exact A.smul_mem hgood (b - a)
  have hxnorm : ‖x‖ < 1 := hnear
  have hAclosed : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A, polynomialUniformClosure]
    exact Subalgebra.isClosed_topologicalClosure _
  have hy : y ∈ A :=
    geometric_sum_mem_closedSubalgebra hAclosed hx
      (summable_geometric_of_norm_lt_one hxnorm).hasSum
  have hyid : y * (1 - x) = 1 := geom_series_mul_neg x hxnorm
  have hformula : resolventOn K b hb = resolventOn K a ha * y := by
    ext z
    have hza : (z : ℂ) - a ≠ 0 := fun h ↦ ha (by
      have hz : (z : ℂ) = a := sub_eq_zero.mp h
      rw [← hz]
      exact z.property)
    have hzb : (z : ℂ) - b ≠ 0 := fun h ↦ hb (by
      have hz : (z : ℂ) = b := sub_eq_zero.mp h
      rw [← hz]
      exact z.property)
    have hyid_z := DFunLike.congr_fun hyid z
    change y z * (1 - (b - a) * (((z : ℂ) - a)⁻¹)) = 1 at hyid_z
    simp only [resolventOn_apply]
    field_simp [hza] at hyid_z
    have hyid_z' : y z * ((z : ℂ) - b) = (z : ℂ) - a := by
      calc
        y z * ((z : ℂ) - b) = y z * ((z : ℂ) - a - (b - a)) := by ring
        _ = (z : ℂ) - a := hyid_z
    apply inv_eq_of_mul_eq_one_left
    calc
      (((z : ℂ) - a)⁻¹ * y z) * ((z : ℂ) - b) =
          (y z * ((z : ℂ) - b)) * ((z : ℂ) - a)⁻¹ := by ring
      _ = ((z : ℂ) - a) * ((z : ℂ) - a)⁻¹ := by rw [hyid_z']
      _ = 1 := mul_inv_cancel₀ hza
  rw [hformula]
  exact A.mul_mem hgood hy

/-- A pole outside a circle containing `K` is good, by expanding its resolvent as a geometric
series in the coordinate function. -/
lemma resolvent_mem_of_norm_lt {K : Set ℂ} [CompactSpace K] [Nonempty K]
    {a : ℂ} (ha : a ∉ K)
    (hfar : ∀ z : K, ‖(z : ℂ)‖ < ‖a‖) :
    resolventOn K a ha ∈ polynomialUniformClosure K := by
  have ha0 : a ≠ 0 := by
    intro ha_zero
    obtain ⟨z⟩ := ‹Nonempty K›
    have hzneg : ‖(z : ℂ)‖ < 0 := by simpa [ha_zero] using hfar z
    exact (not_lt_of_ge (norm_nonneg _)) hzneg
  let A : Subalgebra ℂ C(K, ℂ) := polynomialUniformClosure K
  let X : C(K, ℂ) := Polynomial.X.toContinuousMapOn K
  let x : C(K, ℂ) := a⁻¹ • X
  let y : C(K, ℂ) := ∑' n : ℕ, x ^ n
  have hX : X ∈ A := polynomial_mem_uniformClosure K Polynomial.X
  have hx : x ∈ A := A.smul_mem hX a⁻¹
  have hxnorm : ‖x‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff (f := x) zero_lt_one]
    intro z
    simp only [x, X, ContinuousMap.smul_apply, smul_eq_mul,
      Polynomial.toContinuousMapOn_X_eq_restrict_id, ContinuousMap.restrict_apply,
      ContinuousMap.id_apply]
    rw [norm_mul, norm_inv, inv_mul_lt_one₀ (norm_pos_iff.mpr ha0)]
    exact hfar z
  have hAclosed : IsClosed (A : Set C(K, ℂ)) := by
    dsimp [A, polynomialUniformClosure]
    exact Subalgebra.isClosed_topologicalClosure _
  have hy : y ∈ A :=
    geometric_sum_mem_closedSubalgebra hAclosed hx
      (summable_geometric_of_norm_lt_one hxnorm).hasSum
  have hyid : y * (1 - x) = 1 := geom_series_mul_neg x hxnorm
  have hformula : resolventOn K a ha = (-a⁻¹) • y := by
    ext z
    have hza : (z : ℂ) - a ≠ 0 := fun h ↦ ha (by
      have hz : (z : ℂ) = a := sub_eq_zero.mp h
      rw [← hz]
      exact z.property)
    have hyid_z := DFunLike.congr_fun hyid z
    have hyid_z' : y z * (1 - a⁻¹ * (z : ℂ)) = 1 := by
      simpa only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        x, X, ContinuousMap.smul_apply, smul_eq_mul, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_X_eq_id, ContinuousMap.id_apply] using hyid_z
    simp only [resolventOn_apply]
    apply inv_eq_of_mul_eq_one_left
    calc
      ((-a⁻¹) * y z) * ((z : ℂ) - a) =
          y z * (1 - a⁻¹ * (z : ℂ)) := by field_simp; ring
      _ = 1 := hyid_z'
  rw [hformula]
  exact A.smul_mem hy (-a⁻¹)

/-- The resolvent as a continuous function of its pole in `Kᶜ`, with values in the uniform norm
on `K`. -/
noncomputable def poleResolventMap (K : Set ℂ) [CompactSpace K] : C((Kᶜ : Set ℂ), C(K, ℂ)) where
  toFun a := resolventOn K a a.property
  continuous_toFun := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hsub : Continuous (fun p : (Kᶜ : Set ℂ) × K ↦ (p.2 : ℂ) - (p.1 : ℂ)) :=
      (continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst)
    exact hsub.inv₀ fun p hp ↦ p.1.property (by
      have heq : (p.2 : ℂ) = (p.1 : ℂ) := sub_eq_zero.mp hp
      rw [← heq]
      exact p.2.property)

@[simp] lemma poleResolventMap_apply (K : Set ℂ) [CompactSpace K]
    (a : (Kᶜ : Set ℂ)) (z : K) :
    poleResolventMap K a z = ((z : ℂ) - (a : ℂ))⁻¹ := rfl

lemma poleResolventMap_eq_resolvent (K : Set ℂ) [CompactSpace K]
    (a : (Kᶜ : Set ℂ)) (ha : (a : ℂ) ∉ K) :
    poleResolventMap K a = resolventOn K (a : ℂ) ha := by
  ext z
  rfl

/-- Poles whose resolvents are uniform limits of polynomial restrictions. -/
noncomputable def goodPoleSet (K : Set ℂ) [CompactSpace K] : Set (Kᶜ : Set ℂ) :=
  {a | poleResolventMap K a ∈ polynomialUniformClosure K}

lemma isClosed_goodPoleSet (K : Set ℂ) [CompactSpace K] : IsClosed (goodPoleSet K) := by
  apply (show IsClosed (polynomialUniformClosure K : Set C(K, ℂ)) by
    unfold polynomialUniformClosure
    exact Subalgebra.isClosed_topologicalClosure _).preimage
  exact (poleResolventMap K).continuous

lemma isOpen_goodPoleSet (K : Set ℂ) [CompactSpace K] : IsOpen (goodPoleSet K) := by
  rw [Metric.isOpen_iff]
  intro a ha
  let R : ℝ := ‖poleResolventMap K a‖
  let δ : ℝ := (R + 1)⁻¹
  have hR0 : 0 ≤ R := norm_nonneg _
  have hRp : 0 < R + 1 := by linarith
  have hδp : 0 < δ := inv_pos.mpr hRp
  refine ⟨δ, hδp, ?_⟩
  intro b hb
  have hab : ‖(b : ℂ) - (a : ℂ)‖ < δ := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, Complex.dist_eq] using hb
  have hδR : δ * R < 1 := by
    change (R + 1)⁻¹ * R < 1
    rw [inv_mul_lt_one₀ hRp]
    linarith
  have hnear : ‖((b : ℂ) - (a : ℂ)) • poleResolventMap K a‖ < 1 := by
    rw [norm_smul]
    by_cases hR : R = 0
    · simp [R, hR]
    · calc
        ‖(b : ℂ) - (a : ℂ)‖ * ‖poleResolventMap K a‖ < δ * R := by
          exact mul_lt_mul_of_pos_right hab (lt_of_le_of_ne hR0 (Ne.symm hR))
        _ < 1 := hδR
  have haK : (a : ℂ) ∉ K := a.property
  have hbK : (b : ℂ) ∉ K := b.property
  have hgood : resolventOn K (a : ℂ) haK ∈ polynomialUniformClosure K := by
    change poleResolventMap K a ∈ polynomialUniformClosure K at ha
    rwa [poleResolventMap_eq_resolvent K a haK] at ha
  have := resolvent_mem_of_nearby haK hbK hgood (by
    rwa [poleResolventMap_eq_resolvent K a haK] at hnear)
  change poleResolventMap K b ∈ polynomialUniformClosure K
  rwa [poleResolventMap_eq_resolvent K b hbK]

/-- Runge's pole-moving conclusion: if the complement of a nonempty compact set is connected,
every resolvent with pole in that complement is a uniform limit of polynomial restrictions. -/
lemma resolvent_mem_uniformClosure_of_connected_compl {K : Set ℂ} [CompactSpace K] [Nonempty K]
    (hconn : IsConnected (Kᶜ)) {a : ℂ} (ha : a ∉ K) :
    resolventOn K a ha ∈ polynomialUniformClosure K := by
  letI : ConnectedSpace (Kᶜ : Set ℂ) := Subtype.connectedSpace hconn
  have hKcompact : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨R, hR⟩ := hKcompact.isBounded.subset_ball (0 : ℂ)
  obtain ⟨z₀⟩ := ‹Nonempty K›
  have hRp : 0 < R := by
    have hz : dist (z₀ : ℂ) 0 < R := hR z₀.property
    exact lt_of_le_of_lt dist_nonneg hz
  let b : ℂ := (R + 1 : ℝ)
  have hb_norm : ‖b‖ = R + 1 := by
    calc
      ‖b‖ = ‖((R + 1 : ℝ) : ℂ)‖ := by simp [b]
      _ = |R + 1| := Complex.norm_real _
      _ = R + 1 := abs_of_pos (by linarith)
  have hbK : b ∉ K := by
    intro hb
    have hlt := hR hb
    simp only [Metric.mem_ball, dist_zero_right, hb_norm] at hlt
    linarith
  have hbfar : ∀ z : K, ‖(z : ℂ)‖ < ‖b‖ := by
    intro z
    have hlt := hR z.property
    simp only [Metric.mem_ball, dist_zero_right, hb_norm] at hlt ⊢
    linarith
  let b' : (Kᶜ : Set ℂ) := ⟨b, hbK⟩
  have hbGood : b' ∈ goodPoleSet K := by
    change poleResolventMap K b' ∈ polynomialUniformClosure K
    rw [poleResolventMap_eq_resolvent K b' hbK]
    exact resolvent_mem_of_norm_lt hbK hbfar
  have hclopen : IsClopen (goodPoleSet K) :=
    ⟨isClosed_goodPoleSet K, isOpen_goodPoleSet K⟩
  have hgood_univ : goodPoleSet K = Set.univ := hclopen.eq_univ ⟨b', hbGood⟩
  let a' : (Kᶜ : Set ℂ) := ⟨a, ha⟩
  have haGood : a' ∈ goodPoleSet K := by rw [hgood_univ]; trivial
  change poleResolventMap K a' ∈ polynomialUniformClosure K at haGood
  rwa [poleResolventMap_eq_resolvent K a' ha] at haGood

/-- A path in the complement suffices for pole-moving; global connectedness is unnecessary. -/
lemma resolvent_mem_uniformClosure_of_joined {K : Set ℂ} [CompactSpace K] [Nonempty K]
    {a b : ℂ} (ha : a ∉ K) (hb : b ∉ K) (hbfar : ∀ z : K, ‖(z : ℂ)‖ < ‖b‖)
    (hjoin : JoinedIn Kᶜ b a) :
    resolventOn K a ha ∈ polynomialUniformClosure K := by
  let b' : (Kᶜ : Set ℂ) := ⟨b, hb⟩
  let a' : (Kᶜ : Set ℂ) := ⟨a, ha⟩
  let γ : Path b' a' := hjoin.joined_subtype.somePath
  have hbGood : b' ∈ goodPoleSet K := by
    change poleResolventMap K b' ∈ polynomialUniformClosure K
    rw [poleResolventMap_eq_resolvent K b' hb]
    exact resolvent_mem_of_norm_lt hb hbfar
  have hgoodClopen : IsClopen (goodPoleSet K) :=
    ⟨isClosed_goodPoleSet K, isOpen_goodPoleSet K⟩
  have hpre : IsClopen (γ ⁻¹' goodPoleSet K) := hgoodClopen.preimage γ.continuous
  have hzero : (0 : I) ∈ γ ⁻¹' goodPoleSet K := by
    simpa [γ] using hbGood
  have hpre_univ : γ ⁻¹' goodPoleSet K = Set.univ := hpre.eq_univ ⟨0, hzero⟩
  have hone : (1 : I) ∈ γ ⁻¹' goodPoleSet K := by rw [hpre_univ]; trivial
  have haGood : a' ∈ goodPoleSet K := by simpa [γ] using hone
  change poleResolventMap K a' ∈ polynomialUniformClosure K at haGood
  rwa [poleResolventMap_eq_resolvent K a' ha] at haGood

/-- The reciprocal of a polynomial on a compact set avoiding all of its zeros. -/
noncomputable def polynomialReciprocalOn (K : Set ℂ) (p : Polynomial ℂ)
    (hp : ∀ z : K, p.eval (z : ℂ) ≠ 0) : C(K, ℂ) where
  toFun z := (p.eval (z : ℂ))⁻¹
  continuous_toFun := (p.toContinuousMapOn K).continuous.inv₀ hp

@[simp] lemma polynomialReciprocalOn_apply (K : Set ℂ) (p : Polynomial ℂ)
    (hp : ∀ z : K, p.eval (z : ℂ) ≠ 0) (z : K) :
    polynomialReciprocalOn K p hp z = (p.eval (z : ℂ))⁻¹ := rfl

/-- A polynomial reciprocal is a finite product of its root resolvents. -/
lemma polynomialReciprocal_mem_uniformClosure_of_resolvents
    {K : Set ℂ} [CompactSpace K] [Nonempty K]
    (p : Polynomial ℂ) (hp0 : p ≠ 0) (hroots : ∀ a ∈ p.roots, a ∉ K)
    (hres : ∀ a (ha : a ∈ p.roots),
      resolventOn K a (hroots a ha) ∈ polynomialUniformClosure K) :
    polynomialReciprocalOn K p (fun z hz ↦
      hroots z (Polynomial.mem_roots hp0 |>.mpr hz) z.property) ∈
      polynomialUniformClosure K := by
  let hzero : ∀ z : K, p.eval (z : ℂ) ≠ 0 := fun z hz ↦
    hroots z (Polynomial.mem_roots hp0 |>.mpr hz) z.property
  let rootResolvent : ℂ → C(K, ℂ) := fun a ↦
    if ha : a ∈ p.roots then resolventOn K a (hroots a ha) else 0
  let q : C(K, ℂ) := p.leadingCoeff⁻¹ • (p.roots.map rootResolvent).prod
  have hprod : (p.roots.map rootResolvent).prod ∈ polynomialUniformClosure K := by
    apply (polynomialUniformClosure K).toSubmonoid.multiset_prod_mem
    intro g hg
    rw [Multiset.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    simp only [rootResolvent, dif_pos ha]
    exact hres a ha
  have hq : q ∈ polynomialUniformClosure K :=
    (polynomialUniformClosure K).smul_mem hprod p.leadingCoeff⁻¹
  have heq : polynomialReciprocalOn K p hzero = q := by
    ext z
    have hmap : p.roots.map (fun a ↦ rootResolvent a z) =
        p.roots.map (fun a ↦ ((z : ℂ) - a)⁻¹) := by
      apply Multiset.map_congr rfl
      intro a ha
      simp only [rootResolvent, dif_pos ha, resolventOn_apply]
    have hprod_apply : (p.roots.map rootResolvent).prod z =
        (p.roots.map (fun a ↦ rootResolvent a z)).prod := by
      generalize p.roots = s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons a s ih => simp [ih]
    rw [polynomialReciprocalOn_apply]
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots]
    simp only [q, ContinuousMap.smul_apply, smul_eq_mul]
    rw [hprod_apply, hmap, mul_inv, Multiset.prod_map_inv]
  rw [heq]
  exact hq

/-- The reciprocal of any nonzero polynomial whose roots lie in the connected complement belongs
to the polynomial uniform closure. -/
lemma polynomialReciprocal_mem_uniformClosure {K : Set ℂ} [CompactSpace K] [Nonempty K]
    (hconn : IsConnected (Kᶜ)) (p : Polynomial ℂ) (hp0 : p ≠ 0)
    (hroots : ∀ a ∈ p.roots, a ∉ K) :
    polynomialReciprocalOn K p (fun z hz ↦
      hroots z (Polynomial.mem_roots hp0 |>.mpr hz) z.property) ∈
      polynomialUniformClosure K := by
  apply polynomialReciprocal_mem_uniformClosure_of_resolvents p hp0 hroots
  intro a ha
  exact resolvent_mem_uniformClosure_of_connected_compl hconn (hroots a ha)

/-- The compact set on which a barrier polynomial is prescribed: the unit disk together with one
spiral wall. -/
noncomputable def spiralApproximationSet (k : ℕ) : Set ℂ :=
  Metric.closedBall 0 1 ∪ spiralSet k 1

lemma isCompact_spiralApproximationSet (k : ℕ) : IsCompact (spiralApproximationSet k) :=
  (isCompact_closedBall 0 1).union (isCompact_spiralSet k 1)

instance instNonemptySpiralApproximationSet (k : ℕ) : Nonempty (spiralApproximationSet k) :=
  ⟨⟨0, by left; simp [spiralApproximationSet]⟩⟩

lemma norm_bounds_of_mem_spiralApproximationSet {k : ℕ} {z : ℂ}
    (hz : z ∈ spiralApproximationSet k) :
    ‖z‖ ≤ 1 ∨ (2 ≤ ‖z‖ ∧ ‖z‖ ≤ 3) := by
  rcases hz with hz | hz
  · exact Or.inl (by simpa [Metric.mem_closedBall, Complex.dist_eq] using hz)
  · exact Or.inr (by simpa using spiralSet_norm_bounds k (by positivity) hz)

/-- A radial graph half a turn away from the barrier spiral.  It gives an explicit route for
moving every separator pole from radius `3/2` to radius `7/2`. -/
noncomputable def oppositeSpiralPoint (k : ℕ) (r : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp
    ((((2 * Real.pi * (k : ℝ) * (r - 2) + Real.pi : ℝ) : ℂ) * Complex.I))

lemma norm_oppositeSpiralPoint (k : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    ‖oppositeSpiralPoint k r‖ = r := by
  simp [oppositeSpiralPoint, Complex.norm_exp, abs_of_nonneg hr]

lemma oppositeSpiralPoint_ne_spiralPoint (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    oppositeSpiralPoint k r ≠ spiralPoint k 1 r := by
  intro h
  have hcancel : Complex.exp
      (((2 * Real.pi * (k : ℝ) * (r - 2) + Real.pi : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((2 * Real.pi * (k : ℝ) * (r - 2) : ℝ) : ℂ) * Complex.I) := by
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr)
    simpa [oppositeSpiralPoint, spiralPoint] using h
  rw [show (((2 * Real.pi * (k : ℝ) * (r - 2) + Real.pi : ℝ) : ℂ) * Complex.I) =
      (((2 * Real.pi * (k : ℝ) * (r - 2) : ℝ) : ℂ) * Complex.I) +
        (Real.pi : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I] at hcancel
  have hzero : Complex.exp
      (((2 * Real.pi * (k : ℝ) * (r - 2) : ℝ) : ℂ) * Complex.I) = 0 := by
    linear_combination (-1 / 2 : ℂ) * hcancel
  exact Complex.exp_ne_zero _ hzero

lemma oppositeSpiralPoint_not_mem_approximationSet (k : ℕ) {r : ℝ}
    (hr₁ : 1 < r) (hr₂ : r < 4) :
    oppositeSpiralPoint k r ∉ spiralApproximationSet k := by
  intro hmem
  rcases hmem with hdisk | hspiral
  · have hnorm_le : ‖oppositeSpiralPoint k r‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hdisk
    rw [norm_oppositeSpiralPoint k (le_trans zero_le_one hr₁.le)] at hnorm_le
    linarith
  · obtain ⟨s, hs, heq⟩ := hspiral
    have hs0 : 0 ≤ s := by linarith [hs.1]
    have hnormeq := congrArg norm heq
    rw [norm_spiralPoint k (by positivity) hs0,
      norm_oppositeSpiralPoint k (le_trans zero_le_one hr₁.le)] at hnormeq
    have hsr : s = r := by linarith
    subst s
    exact oppositeSpiralPoint_ne_spiralPoint k (ne_of_gt (lt_trans zero_lt_one hr₁)) heq.symm

lemma joinedIn_oppositeSpiral (k : ℕ) :
    JoinedIn (spiralApproximationSet k)ᶜ
      (oppositeSpiralPoint k (3 / 2)) (oppositeSpiralPoint k (7 / 2)) := by
  let g : ℝ → ℂ := fun t ↦ oppositeSpiralPoint k (3 / 2 + 2 * t)
  refine JoinedIn.ofLine (f := g) (by dsimp [g, oppositeSpiralPoint]; fun_prop) ?_ ?_ ?_
  · congr 1
    norm_num [g]
  · congr 1
    norm_num [g]
  · rintro z ⟨t, ht, rfl⟩
    exact oppositeSpiralPoint_not_mem_approximationSet k (by
      change 1 < 3 / 2 + 2 * t
      linarith [ht.1]) (by
      change 3 / 2 + 2 * t < 4
      linarith [ht.2])

lemma joinedIn_radius_three_halves_to_opposite (k : ℕ) {a : ℂ}
    (ha : ‖a‖ = 3 / 2) :
    JoinedIn (spiralApproximationSet k)ᶜ a (oppositeSpiralPoint k (3 / 2)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hpath := isPathConnected_sphere hrank (0 : ℂ) (r := 3 / 2) (by norm_num)
  have haSphere : a ∈ Metric.sphere (0 : ℂ) (3 / 2) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ha
  have hcSphere : oppositeSpiralPoint k (3 / 2) ∈ Metric.sphere (0 : ℂ) (3 / 2) := by
    rw [Metric.mem_sphere, dist_zero_right,
      norm_oppositeSpiralPoint k (r := 3 / 2) (by norm_num)]
  apply (hpath.joinedIn a haSphere (oppositeSpiralPoint k (3 / 2)) hcSphere).mono
  intro z hz
  have hnorm : ‖z‖ = 3 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  intro hK
  rcases norm_bounds_of_mem_spiralApproximationSet hK with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

lemma resolvent_mem_spiralApproximationSet_of_norm_eq_three_halves (k : ℕ) {a : ℂ}
    (ha_norm : ‖a‖ = 3 / 2) :
    letI : CompactSpace (spiralApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
    resolventOn (spiralApproximationSet k) a (by
      intro haK
      rcases norm_bounds_of_mem_spiralApproximationSet haK with hsmall | hlarge
      · linarith
      · linarith [hlarge.1]) ∈
      polynomialUniformClosure (spiralApproximationSet k) := by
  letI : CompactSpace (spiralApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
  have haK : a ∉ spiralApproximationSet k := by
    intro haK
    rcases norm_bounds_of_mem_spiralApproximationSet haK with hsmall | hlarge
    · linarith
    · linarith [hlarge.1]
  let b : ℂ := oppositeSpiralPoint k (7 / 2)
  have hb_norm : ‖b‖ = 7 / 2 := by
    exact norm_oppositeSpiralPoint k (r := 7 / 2) (by norm_num)
  have hbK : b ∉ spiralApproximationSet k := by
    exact oppositeSpiralPoint_not_mem_approximationSet k (r := 7 / 2) (by norm_num) (by norm_num)
  have hbfar : ∀ z : spiralApproximationSet k, ‖(z : ℂ)‖ < ‖b‖ := by
    intro z
    rw [hb_norm]
    rcases norm_bounds_of_mem_spiralApproximationSet z.property with hsmall | hlarge
    · linarith
    · linarith [hlarge.2]
  have hjoin : JoinedIn (spiralApproximationSet k)ᶜ b a :=
    (joinedIn_oppositeSpiral k).symm.trans
      (joinedIn_radius_three_halves_to_opposite k ha_norm).symm
  exact resolvent_mem_uniformClosure_of_joined haK hbK hbfar hjoin

/-- Denominator of the explicit rational separator
`1 / (1 + (2z/3)^N)`. -/
noncomputable def separatorDenominator (N : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ N + Polynomial.C (((3 / 2 : ℝ) : ℂ) ^ N)

lemma separatorDenominator_ne_zero {N : ℕ} (hN : N ≠ 0) :
    separatorDenominator N ≠ 0 := by
  intro hzero
  have heval := congrArg (fun p : Polynomial ℂ ↦ p.eval 0) hzero
  simp [separatorDenominator, hN] at heval

lemma norm_eq_three_halves_of_mem_separatorDenominator_roots {N : ℕ} (hN : N ≠ 0)
    {a : ℂ} (ha : a ∈ (separatorDenominator N).roots) :
    ‖a‖ = 3 / 2 := by
  have heval : (separatorDenominator N).eval a = 0 :=
    (Polynomial.mem_roots (separatorDenominator_ne_zero hN)).mp ha
  have heval' : a ^ N + (((3 / 2 : ℝ) : ℂ) ^ N) = 0 := by
    simpa [separatorDenominator] using heval
  have hpow : a ^ N = -(((3 / 2 : ℝ) : ℂ) ^ N) := by
    exact eq_neg_of_add_eq_zero_left heval'
  have hnormpow := congrArg norm hpow
  simp only [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at hnormpow
  exact (pow_left_inj₀ (norm_nonneg a) (by norm_num) hN).mp hnormpow

lemma separatorDenominator_eval_ne_zero (k : ℕ) {N : ℕ} (hN : N ≠ 0)
    (z : spiralApproximationSet k) :
    (separatorDenominator N).eval (z : ℂ) ≠ 0 := by
  intro hz
  have hroot : (z : ℂ) ∈ (separatorDenominator N).roots :=
    (Polynomial.mem_roots (separatorDenominator_ne_zero hN)).mpr hz
  have hnorm := norm_eq_three_halves_of_mem_separatorDenominator_roots hN hroot
  rcases norm_bounds_of_mem_spiralApproximationSet z.property with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

/-- The rational separator `1 / (1 + (2z/3)^N)` restricted to the disk-plus-spiral compact set. -/
noncomputable def separatorRationalOn (k N : ℕ) (hN : N ≠ 0) :
    C(spiralApproximationSet k, ℂ) :=
  (((3 / 2 : ℝ) : ℂ) ^ N) •
    polynomialReciprocalOn (spiralApproximationSet k) (separatorDenominator N)
      (separatorDenominator_eval_ne_zero k hN)

@[simp] lemma separatorRationalOn_apply (k N : ℕ) (hN : N ≠ 0)
    (z : spiralApproximationSet k) :
    separatorRationalOn k N hN z =
      (((3 / 2 : ℝ) : ℂ) ^ N) *
        (((z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N))⁻¹) := by
  simp [separatorRationalOn, separatorDenominator]

lemma separatorRational_mem_uniformClosure (k : ℕ) {N : ℕ} (hN : N ≠ 0) :
    letI : CompactSpace (spiralApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
    separatorRationalOn k N hN ∈ polynomialUniformClosure (spiralApproximationSet k) := by
  letI : CompactSpace (spiralApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
  have hroots : ∀ a ∈ (separatorDenominator N).roots,
      a ∉ spiralApproximationSet k := by
    intro a ha haK
    have hnorm := norm_eq_three_halves_of_mem_separatorDenominator_roots hN ha
    rcases norm_bounds_of_mem_spiralApproximationSet haK with hsmall | hlarge
    · linarith
    · linarith [hlarge.1]
  have hrec := polynomialReciprocal_mem_uniformClosure_of_resolvents
    (separatorDenominator N) (separatorDenominator_ne_zero hN) hroots (by
      intro a ha
      exact resolvent_mem_spiralApproximationSet_of_norm_eq_three_halves k
        (norm_eq_three_halves_of_mem_separatorDenominator_roots hN ha))
  exact (polynomialUniformClosure (spiralApproximationSet k)).smul_mem hrec
    (((3 / 2 : ℝ) : ℂ) ^ N)

/-- A globally continuous radial cutoff which is exactly one on the disk component and zero on the
spiral component of `spiralApproximationSet`. -/
noncomputable def spiralTargetOn (k : ℕ) : C(spiralApproximationSet k, ℂ) where
  toFun z := ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

lemma spiralTargetOn_eq_one {k : ℕ} (z : spiralApproximationSet k) (hz : ‖(z : ℂ)‖ ≤ 1) :
    spiralTargetOn k z = 1 := by
  change ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ) = 1
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  norm_num

lemma spiralTargetOn_eq_zero {k : ℕ} (z : spiralApproximationSet k) (hz : 2 ≤ ‖(z : ℂ)‖) :
    spiralTargetOn k z = 0 := by
  change ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ) = 0
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  norm_num

lemma div_sub_le_three_mul_div {A C : ℝ} (hA : 0 ≤ A) (hC : 0 < C)
    (hAC : A ≤ (2 / 3) * C) :
    A / (C - A) ≤ 3 * A / C := by
  have hden : 0 < C - A := by nlinarith
  rw [div_le_iff₀ hden]
  rw [div_mul_eq_mul_div, le_div_iff₀ hC]
  nlinarith

lemma div_sub_le_four_mul_div {A C : ℝ} (hC : 0 ≤ C) (hA : 0 < A)
    (hCA : C ≤ (3 / 4) * A) :
    C / (A - C) ≤ 4 * C / A := by
  have hden : 0 < A - C := by nlinarith
  rw [div_le_iff₀ hden]
  rw [div_mul_eq_mul_div, le_div_iff₀ hA]
  nlinarith

lemma separatorRational_sub_one_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N)
    (z : spiralApproximationSet k) (hz : ‖(z : ℂ)‖ ≤ 1) :
    ‖separatorRationalOn k N hN.ne' z - 1‖ ≤ 4 * (3 / 4 : ℝ) ^ N := by
  let A : ℝ := ‖(z : ℂ) ^ N‖
  let C : ℝ := (3 / 2 : ℝ) ^ N
  have hA0 : 0 ≤ A := norm_nonneg _
  have hA1 : A ≤ 1 := by
    dsimp [A]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hCp : 0 < C := pow_pos (by norm_num) _
  have hCbig : 3 / 2 ≤ C := by
    calc
      (3 / 2 : ℝ) = (3 / 2 : ℝ) ^ 1 := by ring
      _ ≤ (3 / 2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hAC : A ≤ (2 / 3 : ℝ) * C := by nlinarith
  have hdenpos : 0 < C - A := by nlinarith
  have hden : C - A ≤
      ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by
    calc
      C - A = ‖(((3 / 2 : ℝ) : ℂ) ^ N)‖ - ‖(z : ℂ) ^ N‖ := by
        simp [C, A]
      _ ≤ ‖(((3 / 2 : ℝ) : ℂ) ^ N) - (-((z : ℂ) ^ N))‖ :=
        by simpa only [norm_neg] using
          norm_sub_norm_le (((3 / 2 : ℝ) : ℂ) ^ N) (-((z : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by ring_nf
  have hdenzero : (z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N) ≠ 0 := by
    simpa [separatorDenominator] using separatorDenominator_eval_ne_zero k hN.ne' z
  have hformula : separatorRationalOn k N hN.ne' z - 1 =
      (-((z : ℂ) ^ N)) *
        (((z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N))⁻¹) := by
    rw [separatorRationalOn_apply]
    field_simp
    ring
  rw [hformula, norm_mul, norm_neg, norm_inv]
  change A * ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  calc
    A / ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ ≤ A / (C - A) := by
      exact div_le_div_of_nonneg_left hA0 hdenpos hden
    _ ≤ 3 * A / C := div_sub_le_three_mul_div hA0 hCp hAC
    _ ≤ 3 * (2 / 3 : ℝ) ^ N := by
      have hcinv : C⁻¹ = (2 / 3 : ℝ) ^ N := by
        dsimp [C]
        rw [← inv_pow]
        congr 1 <;> norm_num
      rw [div_eq_mul_inv, hcinv]
      have h3A : 3 * A ≤ 3 := by nlinarith
      exact mul_le_mul_of_nonneg_right h3A
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) N)
    _ ≤ 4 * (3 / 4 : ℝ) ^ N := by
      have hpows : (2 / 3 : ℝ) ^ N ≤ (3 / 4 : ℝ) ^ N := by
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N]

lemma separatorRational_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N)
    (z : spiralApproximationSet k) (hz : 2 ≤ ‖(z : ℂ)‖) :
    ‖separatorRationalOn k N hN.ne' z‖ ≤ 4 * (3 / 4 : ℝ) ^ N := by
  let A : ℝ := ‖(z : ℂ) ^ N‖
  let C : ℝ := (3 / 2 : ℝ) ^ N
  let q : ℝ := (3 / 4 : ℝ) ^ N
  have hApos : 0 < A := by
    dsimp [A]
    rw [norm_pow]
    exact pow_pos (lt_of_lt_of_le (by norm_num) hz) _
  have hC0 : 0 ≤ C := (pow_pos (by norm_num) _).le
  have hq0 : 0 ≤ q := pow_nonneg (by norm_num) _
  have hCqA : C ≤ q * A := by
    have hbase : (3 / 2 : ℝ) ≤ (3 / 4 : ℝ) * ‖(z : ℂ)‖ := by nlinarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hbase N
    simpa only [mul_pow, norm_pow, C, q, A] using hp
  have hqle : q ≤ 3 / 4 := by
    exact pow_le_of_le_one (by norm_num) (by norm_num) hN.ne'
  have hCA : C ≤ (3 / 4 : ℝ) * A :=
    hCqA.trans (mul_le_mul_of_nonneg_right hqle hApos.le)
  have hdenpos : 0 < A - C := by nlinarith
  have hden : A - C ≤
      ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by
    calc
      A - C = ‖(z : ℂ) ^ N‖ - ‖(((3 / 2 : ℝ) : ℂ) ^ N)‖ := by
        simp [C, A]
      _ ≤ ‖(z : ℂ) ^ N - (-(((3 / 2 : ℝ) : ℂ) ^ N))‖ := by
        simpa only [norm_neg] using
          norm_sub_norm_le ((z : ℂ) ^ N) (-(((3 / 2 : ℝ) : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by ring_nf
  rw [separatorRationalOn_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), norm_inv]
  change C * ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  calc
    C / ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ ≤ C / (A - C) := by
      exact div_le_div_of_nonneg_left hC0 hdenpos hden
    _ ≤ 4 * C / A := div_sub_le_four_mul_div hC0 hApos hCA
    _ ≤ 4 * q := by
      rw [div_le_iff₀ hApos]
      nlinarith
    _ = 4 * (3 / 4 : ℝ) ^ N := rfl

lemma separatorRational_sub_target_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N) :
    letI : CompactSpace (spiralApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
    ‖separatorRationalOn k N hN.ne' - spiralTargetOn k‖ ≤
      4 * (3 / 4 : ℝ) ^ N := by
  letI : CompactSpace (spiralApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro z
  rcases norm_bounds_of_mem_spiralApproximationSet z.property with hsmall | hlarge
  · rw [ContinuousMap.sub_apply, spiralTargetOn_eq_one z hsmall]
    exact separatorRational_sub_one_norm_le k hN z hsmall
  · rw [ContinuousMap.sub_apply, spiralTargetOn_eq_zero z hlarge.1, sub_zero]
    exact separatorRational_norm_le k hN z hlarge.1

lemma spiralTarget_mem_uniformClosure (k : ℕ) :
    letI : CompactSpace (spiralApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
    spiralTargetOn k ∈ polynomialUniformClosure (spiralApproximationSet k) := by
  letI : CompactSpace (spiralApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
  let F : ℕ → C(spiralApproximationSet k, ℂ) := fun n ↦
    separatorRationalOn k (n + 1) (Nat.succ_ne_zero n)
  have hbound : ∀ n,
      ‖F n - spiralTargetOn k‖ ≤ 4 * (3 / 4 : ℝ) ^ (n + 1) := by
    intro n
    exact separatorRational_sub_target_norm_le k (Nat.succ_pos n)
  have hscalar : Tendsto (fun n : ℕ ↦ 4 * (3 / 4 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      hp.const_mul (4 * (3 / 4 : ℝ))
  have hnorm : Tendsto (fun n ↦ ‖F n - spiralTargetOn k‖) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ norm_nonneg _) hbound hscalar
  have hlim : Tendsto F atTop (𝓝 (spiralTargetOn k)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hclosed : IsClosed
      (polynomialUniformClosure (spiralApproximationSet k) :
        Set C(spiralApproximationSet k, ℂ)) := by
    unfold polynomialUniformClosure
    exact Subalgebra.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hlim
  filter_upwards [] with n
  exact separatorRational_mem_uniformClosure k (Nat.succ_ne_zero n)

/-- The normalized polynomial separator used in every stage of the Gol'dberg--Eremenko product. -/
theorem exists_barrierPolynomial (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.eval 0 = 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖P.eval z - 1‖ < ε) ∧
      (∀ z ∈ spiralSet k 1, ‖P.eval z‖ < ε) := by
  letI : CompactSpace (spiralApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_spiralApproximationSet k)
  let δ : ℝ := min (ε / 8) (1 / 8)
  have hδp : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδeight : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_mem_uniformClosure
    (spiralApproximationSet k) (spiralTargetOn k)
      (spiralTarget_mem_uniformClosure k) hδp
  have hpoint : ∀ z : spiralApproximationSet k,
      ‖q.eval (z : ℂ) - spiralTargetOn k z‖ < δ := by
    intro z
    have hzle := ContinuousMap.norm_coe_le_norm
      (q.toContinuousMapOn (spiralApproximationSet k) - spiralTargetOn k) z
    exact lt_of_le_of_lt (by simpa using hzle) hq
  let z₀ : spiralApproximationSet k := ⟨0, by
    left
    simp [spiralApproximationSet]⟩
  have htarget0 : spiralTargetOn k z₀ = 1 :=
    spiralTargetOn_eq_one z₀ (by simp [z₀])
  have hq0 : ‖q.eval 0 - 1‖ < δ := by
    simpa [z₀, htarget0] using hpoint z₀
  have hq0norm : 1 / 2 < ‖q.eval 0‖ := by
    have hrev : 1 - ‖q.eval 0‖ ≤ ‖q.eval 0 - 1‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le (1 : ℂ) (q.eval 0)
    linarith
  have hq0ne : q.eval 0 ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hq0norm)
  let P : Polynomial ℂ := (q.eval 0)⁻¹ • q
  refine ⟨P, ?_, ?_, ?_⟩
  · simp [P, hq0ne]
  · intro z hz
    let z' : spiralApproximationSet k := ⟨z, by
      left
      simpa [spiralApproximationSet, Metric.mem_closedBall, Complex.dist_eq] using hz⟩
    have htarget : spiralTargetOn k z' = 1 := spiralTargetOn_eq_one z' hz
    have hqz : ‖q.eval z - 1‖ < δ := by
      simpa [z', htarget] using hpoint z'
    have hdiff : ‖q.eval z - q.eval 0‖ < 2 * δ := by
      calc
        ‖q.eval z - q.eval 0‖ = ‖(q.eval z - 1) - (q.eval 0 - 1)‖ := by ring_nf
        _ ≤ ‖q.eval z - 1‖ + ‖q.eval 0 - 1‖ := norm_sub_le _ _
        _ < 2 * δ := by linarith
    have hinv : ‖(q.eval 0)⁻¹‖ < 2 := by
      rw [norm_inv, inv_lt_iff_one_lt_mul₀ (norm_pos_iff.mpr hq0ne)]
      linarith
    have heq : P.eval z - 1 = (q.eval 0)⁻¹ * (q.eval z - q.eval 0) := by
      simp only [P, Polynomial.eval_smul, smul_eq_mul]
      field_simp
    rw [heq, norm_mul]
    have hprod : ‖(q.eval 0)⁻¹‖ * ‖q.eval z - q.eval 0‖ < 2 * (2 * δ) :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hinv.le hdiff (norm_nonneg _) (by norm_num)
    nlinarith

  · intro z hz
    let z' : spiralApproximationSet k := ⟨z, Or.inr hz⟩
    have hlarge : 2 ≤ ‖z‖ := by
      have h := (spiralSet_norm_bounds k (by positivity) hz).1
      norm_num at h ⊢
      exact h
    have htarget : spiralTargetOn k z' = 0 := spiralTargetOn_eq_zero z' hlarge
    have hqz : ‖q.eval z‖ < δ := by
      simpa [z', htarget] using hpoint z'
    have hinv : ‖(q.eval 0)⁻¹‖ < 2 := by
      rw [norm_inv, inv_lt_iff_one_lt_mul₀ (norm_pos_iff.mpr hq0ne)]
      linarith
    simp only [P, Polynomial.eval_smul, smul_eq_mul, norm_mul]
    have hprod : ‖(q.eval 0)⁻¹‖ * ‖q.eval z‖ < 2 * δ :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hinv.le hqz (norm_nonneg _) (by norm_num)
    nlinarith

/-!
## A finite circular labyrinth

For the geometric part it is convenient to replace a continuously winding spiral by the
equivalent ``alternating gates'' labyrinth used in standard proofs of the same theorem.  There
are `k` almost-complete concentric circles between radii `2T` and `3T`; their missing gates
alternate between the right and left half-planes.  A curve crossing all the circles must therefore
make `k - 1` trips of Euclidean length at least `2T`.  Unlike an argument-variation proof for a
spiral, this estimate uses only the intermediate value theorem and the Lipschitz condition.
-/

/-- Radius of the `i`th gate in the normalized annulus. -/
noncomputable def gateRadius (k i : ℕ) : ℝ :=
  2 + (i : ℝ) / (k + 1 : ℝ)

/-- The `i`th almost-complete circle.  Its open gate is centered at `+1` for even `i` and
at `-1` for odd `i`. -/
noncomputable def labyrinthGate (k i : ℕ) (T : ℝ) : Set ℂ :=
  {z | ‖z‖ = T * gateRadius k i ∧
    ((-1 : ℝ) ^ i) * z.re ≤ T * gateRadius k i / 2}

/-- The finite alternating-gate labyrinth at scale `T`. -/
noncomputable def labyrinthSet (k : ℕ) (T : ℝ) : Set ℂ :=
  ⋃ i ∈ Finset.range k, labyrinthGate k i T

lemma gateRadius_bounds {k i : ℕ} (hi : i < k) :
    2 ≤ gateRadius k i ∧ gateRadius k i < 3 := by
  have hk : 0 < (k + 1 : ℝ) := by positivity
  have hi0 : 0 ≤ (i : ℝ) := by positivity
  have hik : (i : ℝ) < (k + 1 : ℝ) := by exact_mod_cast (lt_trans hi (Nat.lt_succ_self k))
  constructor
  · simp only [gateRadius]
    have hdiv : 0 ≤ (i : ℝ) / (k + 1 : ℝ) := div_nonneg hi0 hk.le
    linarith
  · simp only [gateRadius]
    have : (i : ℝ) / (k + 1 : ℝ) < 1 := (div_lt_one hk).2 hik
    linarith

lemma two_le_gateRadius (k i : ℕ) : 2 ≤ gateRadius k i := by
  simp only [gateRadius]
  have hk : 0 ≤ (k + 1 : ℝ) := by positivity
  have hi : 0 ≤ (i : ℝ) := by positivity
  exact le_add_of_nonneg_right (div_nonneg hi hk)

lemma isCompact_labyrinthGate (k i : ℕ) (T : ℝ) :
    IsCompact (labyrinthGate k i T) := by
  have hhalf : IsClosed
      {z : ℂ | ((-1 : ℝ) ^ i) * z.re ≤ T * gateRadius k i / 2} :=
    isClosed_le (continuous_const.mul Complex.continuous_re) continuous_const
  simpa only [labyrinthGate, Metric.sphere, dist_zero_right, Set.mem_setOf_eq,
    Set.setOf_and] using
      (isCompact_sphere (0 : ℂ) (T * gateRadius k i)).inter_right hhalf

lemma isCompact_labyrinthSet (k : ℕ) (T : ℝ) : IsCompact (labyrinthSet k T) := by
  exact (Finset.range k).isCompact_biUnion fun i _ ↦ isCompact_labyrinthGate k i T

lemma labyrinthSet_norm_bounds {k : ℕ} {T : ℝ} (hT : 0 < T) {z : ℂ}
    (hz : z ∈ labyrinthSet k T) :
    2 * T ≤ ‖z‖ ∧ ‖z‖ < 3 * T := by
  simp only [labyrinthSet, Set.mem_iUnion] at hz
  obtain ⟨i, hiRange, hgate⟩ := hz
  have hi' : i < k := Finset.mem_range.mp hiRange
  rw [hgate.1]
  constructor
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left (gateRadius_bounds hi').1 hT.le
  · simpa [mul_comm] using mul_lt_mul_of_pos_left (gateRadius_bounds hi').2 hT

/-- Compact set on which the labyrinth separator is prescribed. -/
noncomputable def labyrinthApproximationSet (k : ℕ) : Set ℂ :=
  Metric.closedBall 0 1 ∪ labyrinthSet k 1

lemma isCompact_labyrinthApproximationSet (k : ℕ) :
    IsCompact (labyrinthApproximationSet k) :=
  (isCompact_closedBall 0 1).union (isCompact_labyrinthSet k 1)

instance instNonemptyLabyrinthApproximationSet (k : ℕ) :
    Nonempty (labyrinthApproximationSet k) :=
  ⟨⟨0, by left; simp [labyrinthApproximationSet]⟩⟩

lemma norm_bounds_of_mem_labyrinthApproximationSet {k : ℕ} {z : ℂ}
    (hz : z ∈ labyrinthApproximationSet k) :
    ‖z‖ ≤ 1 ∨ (2 ≤ ‖z‖ ∧ ‖z‖ < 3) := by
  rcases hz with hz | hz
  · exact Or.inl (by simpa [Metric.mem_closedBall, Complex.dist_eq] using hz)
  · exact Or.inr (by simpa using labyrinthSet_norm_bounds (k := k) (T := 1) (by norm_num) hz)

/-- A continuous route through the centers of all alternating gates. -/
noncomputable def mazePoint (k : ℕ) (r : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp
    ((((Real.pi * (k + 1 : ℝ) * (r - 2) : ℝ) : ℂ) * Complex.I))

lemma norm_mazePoint (k : ℕ) {r : ℝ} (hr : 0 ≤ r) : ‖mazePoint k r‖ = r := by
  simp [mazePoint, Complex.norm_exp, abs_of_nonneg hr]

lemma mazePoint_gateRadius (k i : ℕ) :
    mazePoint k (gateRadius k i) =
      (((gateRadius k i * (-1 : ℝ) ^ i : ℝ) : ℂ)) := by
  have hk0 : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hexponent :
      (((Real.pi * (k + 1 : ℝ) * (gateRadius k i - 2) : ℝ) : ℂ) * Complex.I) =
        (i : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    simp only [gateRadius]
    push_cast
    field_simp
    ring
  rw [mazePoint, hexponent, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  push_cast
  ring

lemma mazePoint_not_mem_labyrinthApproximationSet (k : ℕ) {r : ℝ}
    (hr₁ : 1 < r) (hr₂ : r < 4) :
    mazePoint k r ∉ labyrinthApproximationSet k := by
  intro hmem
  rcases hmem with hdisk | hlab
  · have hnorm_le : ‖mazePoint k r‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hdisk
    rw [norm_mazePoint k (le_trans zero_le_one hr₁.le)] at hnorm_le
    linarith
  · simp only [labyrinthSet, Set.mem_iUnion] at hlab
    obtain ⟨i, hiRange, hiGate⟩ := hlab
    have hi' : i < k := Finset.mem_range.mp hiRange
    have hnormeq := hiGate.1
    rw [norm_mazePoint k (le_trans zero_le_one hr₁.le)] at hnormeq
    have hradius : r = gateRadius k i := by simpa using hnormeq
    subst r
    simp only [one_mul] at hiGate
    rw [mazePoint_gateRadius] at hiGate
    simp only [labyrinthGate, Complex.ofReal_re, one_mul] at hiGate
    have hsignsq : ((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hsignre : (((-1 : ℂ) ^ i).re) = (-1 : ℝ) ^ i := by
      have hpow : (-1 : ℂ) ^ i = (((-1 : ℝ) ^ i : ℝ) : ℂ) := by
        calc
          (-1 : ℂ) ^ i = (((-1 : ℝ) : ℂ) ^ i) := by congr 2 <;> norm_num
          _ = (((-1 : ℝ) ^ i : ℝ) : ℂ) := (Complex.ofReal_pow (-1) i).symm
      rw [hpow]
      exact Complex.ofReal_re _
    have hrpos : 0 < gateRadius k i := lt_of_lt_of_le (by norm_num) (gateRadius_bounds hi').1
    have hineq : ((-1 : ℝ) ^ i) * (gateRadius k i * (-1 : ℝ) ^ i) ≤
        gateRadius k i / 2 := by
      simpa [hsignre] using hiGate.2
    have heq : ((-1 : ℝ) ^ i) * (gateRadius k i * (-1 : ℝ) ^ i) =
        gateRadius k i := by
      calc
        _ = gateRadius k i * (((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i)) := by ring
        _ = gateRadius k i := by rw [hsignsq, mul_one]
    rw [heq] at hineq
    linarith

lemma joinedIn_mazePoint (k : ℕ) :
    JoinedIn (labyrinthApproximationSet k)ᶜ
      (mazePoint k (3 / 2)) (mazePoint k (7 / 2)) := by
  let g : ℝ → ℂ := fun t ↦ mazePoint k (3 / 2 + 2 * t)
  refine JoinedIn.ofLine (f := g) (by dsimp [g, mazePoint]; fun_prop) ?_ ?_ ?_
  · norm_num [g]
  · norm_num [g]
  · rintro z ⟨t, ht, rfl⟩
    exact mazePoint_not_mem_labyrinthApproximationSet k (by
      change 1 < 3 / 2 + 2 * t
      linarith [ht.1]) (by
      change 3 / 2 + 2 * t < 4
      linarith [ht.2])

lemma joinedIn_radius_three_halves_to_mazePoint (k : ℕ) {a : ℂ}
    (ha : ‖a‖ = 3 / 2) :
    JoinedIn (labyrinthApproximationSet k)ᶜ a (mazePoint k (3 / 2)) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hpath := isPathConnected_sphere hrank (0 : ℂ) (r := 3 / 2) (by norm_num)
  have haSphere : a ∈ Metric.sphere (0 : ℂ) (3 / 2) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ha
  have hcSphere : mazePoint k (3 / 2) ∈ Metric.sphere (0 : ℂ) (3 / 2) := by
    rw [Metric.mem_sphere, dist_zero_right, norm_mazePoint k (r := 3 / 2) (by norm_num)]
  apply (hpath.joinedIn a haSphere (mazePoint k (3 / 2)) hcSphere).mono
  intro z hz
  have hnorm : ‖z‖ = 3 / 2 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  intro hK
  rcases norm_bounds_of_mem_labyrinthApproximationSet hK with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

lemma resolvent_mem_labyrinthApproximationSet_of_norm_eq_three_halves (k : ℕ) {a : ℂ}
    (ha_norm : ‖a‖ = 3 / 2) :
    letI : CompactSpace (labyrinthApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
    resolventOn (labyrinthApproximationSet k) a (by
      intro haK
      rcases norm_bounds_of_mem_labyrinthApproximationSet haK with hsmall | hlarge
      · linarith
      · linarith [hlarge.1]) ∈
      polynomialUniformClosure (labyrinthApproximationSet k) := by
  letI : CompactSpace (labyrinthApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
  have haK : a ∉ labyrinthApproximationSet k := by
    intro haK
    rcases norm_bounds_of_mem_labyrinthApproximationSet haK with hsmall | hlarge
    · linarith
    · linarith [hlarge.1]
  let b : ℂ := mazePoint k (7 / 2)
  have hb_norm : ‖b‖ = 7 / 2 := norm_mazePoint k (r := 7 / 2) (by norm_num)
  have hbK : b ∉ labyrinthApproximationSet k :=
    mazePoint_not_mem_labyrinthApproximationSet k (r := 7 / 2) (by norm_num) (by norm_num)
  have hbfar : ∀ z : labyrinthApproximationSet k, ‖(z : ℂ)‖ < ‖b‖ := by
    intro z
    rw [hb_norm]
    rcases norm_bounds_of_mem_labyrinthApproximationSet z.property with hsmall | hlarge
    · linarith
    · linarith [hlarge.2]
  have hjoin : JoinedIn (labyrinthApproximationSet k)ᶜ b a :=
    (joinedIn_mazePoint k).symm.trans
      (joinedIn_radius_three_halves_to_mazePoint k ha_norm).symm
  exact resolvent_mem_uniformClosure_of_joined haK hbK hbfar hjoin

lemma separatorDenominator_eval_ne_zero_labyrinth (k : ℕ) {N : ℕ} (hN : N ≠ 0)
    (z : labyrinthApproximationSet k) :
    (separatorDenominator N).eval (z : ℂ) ≠ 0 := by
  intro hz
  have hroot : (z : ℂ) ∈ (separatorDenominator N).roots :=
    (Polynomial.mem_roots (separatorDenominator_ne_zero hN)).mpr hz
  have hnorm := norm_eq_three_halves_of_mem_separatorDenominator_roots hN hroot
  rcases norm_bounds_of_mem_labyrinthApproximationSet z.property with hsmall | hlarge
  · linarith
  · linarith [hlarge.1]

/-- The same explicit rational separator, now restricted to the disk-plus-labyrinth compact set. -/
noncomputable def labyrinthSeparatorRationalOn (k N : ℕ) (hN : N ≠ 0) :
    C(labyrinthApproximationSet k, ℂ) :=
  (((3 / 2 : ℝ) : ℂ) ^ N) •
    polynomialReciprocalOn (labyrinthApproximationSet k) (separatorDenominator N)
      (separatorDenominator_eval_ne_zero_labyrinth k hN)

@[simp] lemma labyrinthSeparatorRationalOn_apply (k N : ℕ) (hN : N ≠ 0)
    (z : labyrinthApproximationSet k) :
    labyrinthSeparatorRationalOn k N hN z =
      (((3 / 2 : ℝ) : ℂ) ^ N) *
        (((z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N))⁻¹) := by
  simp [labyrinthSeparatorRationalOn, separatorDenominator]

lemma labyrinthSeparatorRational_mem_uniformClosure (k : ℕ) {N : ℕ} (hN : N ≠ 0) :
    letI : CompactSpace (labyrinthApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
    labyrinthSeparatorRationalOn k N hN ∈
      polynomialUniformClosure (labyrinthApproximationSet k) := by
  letI : CompactSpace (labyrinthApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
  have hroots : ∀ a ∈ (separatorDenominator N).roots,
      a ∉ labyrinthApproximationSet k := by
    intro a ha haK
    have hnorm := norm_eq_three_halves_of_mem_separatorDenominator_roots hN ha
    rcases norm_bounds_of_mem_labyrinthApproximationSet haK with hsmall | hlarge
    · linarith
    · linarith [hlarge.1]
  have hrec := polynomialReciprocal_mem_uniformClosure_of_resolvents
    (separatorDenominator N) (separatorDenominator_ne_zero hN) hroots (by
      intro a ha
      exact resolvent_mem_labyrinthApproximationSet_of_norm_eq_three_halves k
        (norm_eq_three_halves_of_mem_separatorDenominator_roots hN ha))
  exact (polynomialUniformClosure (labyrinthApproximationSet k)).smul_mem hrec
    (((3 / 2 : ℝ) : ℂ) ^ N)

/-- Radial target equal to one on the disk and zero on every circular gate. -/
noncomputable def labyrinthTargetOn (k : ℕ) : C(labyrinthApproximationSet k, ℂ) where
  toFun z := ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

lemma labyrinthTargetOn_eq_one {k : ℕ} (z : labyrinthApproximationSet k)
    (hz : ‖(z : ℂ)‖ ≤ 1) : labyrinthTargetOn k z = 1 := by
  change ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ) = 1
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]
  norm_num

lemma labyrinthTargetOn_eq_zero {k : ℕ} (z : labyrinthApproximationSet k)
    (hz : 2 ≤ ‖(z : ℂ)‖) : labyrinthTargetOn k z = 0 := by
  change ((max 0 (min 1 (2 - ‖(z : ℂ)‖)) : ℝ) : ℂ) = 0
  rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  norm_num

lemma labyrinthSeparatorRational_sub_one_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N)
    (z : labyrinthApproximationSet k) (hz : ‖(z : ℂ)‖ ≤ 1) :
    ‖labyrinthSeparatorRationalOn k N hN.ne' z - 1‖ ≤ 4 * (3 / 4 : ℝ) ^ N := by
  let A : ℝ := ‖(z : ℂ) ^ N‖
  let C : ℝ := (3 / 2 : ℝ) ^ N
  have hA0 : 0 ≤ A := norm_nonneg _
  have hA1 : A ≤ 1 := by
    dsimp [A]
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hz
  have hCp : 0 < C := pow_pos (by norm_num) _
  have hCbig : 3 / 2 ≤ C := by
    calc
      (3 / 2 : ℝ) = (3 / 2 : ℝ) ^ 1 := by ring
      _ ≤ (3 / 2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hN
  have hAC : A ≤ (2 / 3 : ℝ) * C := by nlinarith
  have hdenpos : 0 < C - A := by nlinarith
  have hden : C - A ≤
      ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by
    calc
      C - A = ‖(((3 / 2 : ℝ) : ℂ) ^ N)‖ - ‖(z : ℂ) ^ N‖ := by simp [C, A]
      _ ≤ ‖(((3 / 2 : ℝ) : ℂ) ^ N) - (-((z : ℂ) ^ N))‖ := by
        simpa only [norm_neg] using
          norm_sub_norm_le (((3 / 2 : ℝ) : ℂ) ^ N) (-((z : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by ring_nf
  have hdenzero : (z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N) ≠ 0 := by
    simpa [separatorDenominator] using
      separatorDenominator_eval_ne_zero_labyrinth k hN.ne' z
  have hformula : labyrinthSeparatorRationalOn k N hN.ne' z - 1 =
      (-((z : ℂ) ^ N)) *
        (((z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N))⁻¹) := by
    rw [labyrinthSeparatorRationalOn_apply]
    field_simp [hdenzero]
    ring
  rw [hformula, norm_mul, norm_neg, norm_inv]
  change A * ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  calc
    A / ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ ≤ A / (C - A) := by
      exact div_le_div_of_nonneg_left hA0 hdenpos hden
    _ ≤ 3 * A / C := div_sub_le_three_mul_div hA0 hCp hAC
    _ ≤ 3 * (2 / 3 : ℝ) ^ N := by
      have hcinv : C⁻¹ = (2 / 3 : ℝ) ^ N := by
        dsimp [C]
        rw [← inv_pow]
        congr 1 <;> norm_num
      rw [div_eq_mul_inv, hcinv]
      have h3A : 3 * A ≤ 3 := by nlinarith
      exact mul_le_mul_of_nonneg_right h3A
        (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) N)
    _ ≤ 4 * (3 / 4 : ℝ) ^ N := by
      have hpows : (2 / 3 : ℝ) ^ N ≤ (3 / 4 : ℝ) ^ N :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) N]

lemma labyrinthSeparatorRational_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N)
    (z : labyrinthApproximationSet k) (hz : 2 ≤ ‖(z : ℂ)‖) :
    ‖labyrinthSeparatorRationalOn k N hN.ne' z‖ ≤ 4 * (3 / 4 : ℝ) ^ N := by
  let A : ℝ := ‖(z : ℂ) ^ N‖
  let C : ℝ := (3 / 2 : ℝ) ^ N
  let q : ℝ := (3 / 4 : ℝ) ^ N
  have hApos : 0 < A := by
    dsimp [A]
    rw [norm_pow]
    exact pow_pos (lt_of_lt_of_le (by norm_num) hz) _
  have hC0 : 0 ≤ C := (pow_pos (by norm_num) _).le
  have hq0 : 0 ≤ q := pow_nonneg (by norm_num) _
  have hCqA : C ≤ q * A := by
    have hbase : (3 / 2 : ℝ) ≤ (3 / 4 : ℝ) * ‖(z : ℂ)‖ := by nlinarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hbase N
    simpa only [mul_pow, norm_pow, C, q, A] using hp
  have hqle : q ≤ 3 / 4 :=
    pow_le_of_le_one (by norm_num) (by norm_num) hN.ne'
  have hCA : C ≤ (3 / 4 : ℝ) * A :=
    hCqA.trans (mul_le_mul_of_nonneg_right hqle hApos.le)
  have hdenpos : 0 < A - C := by nlinarith
  have hden : A - C ≤
      ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by
    calc
      A - C = ‖(z : ℂ) ^ N‖ - ‖(((3 / 2 : ℝ) : ℂ) ^ N)‖ := by simp [C, A]
      _ ≤ ‖(z : ℂ) ^ N - (-(((3 / 2 : ℝ) : ℂ) ^ N))‖ := by
        simpa only [norm_neg] using
          norm_sub_norm_le ((z : ℂ) ^ N) (-(((3 / 2 : ℝ) : ℂ) ^ N))
      _ = ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ := by ring_nf
  rw [labyrinthSeparatorRationalOn_apply, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2), norm_inv]
  change C * ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖⁻¹ ≤ _
  rw [← div_eq_mul_inv]
  calc
    C / ‖(z : ℂ) ^ N + (((3 / 2 : ℝ) : ℂ) ^ N)‖ ≤ C / (A - C) := by
      exact div_le_div_of_nonneg_left hC0 hdenpos hden
    _ ≤ 4 * C / A := div_sub_le_four_mul_div hC0 hApos hCA
    _ ≤ 4 * q := by
      rw [div_le_iff₀ hApos]
      nlinarith
    _ = 4 * (3 / 4 : ℝ) ^ N := rfl

lemma labyrinthSeparatorRational_sub_target_norm_le (k : ℕ) {N : ℕ} (hN : 0 < N) :
    letI : CompactSpace (labyrinthApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
    ‖labyrinthSeparatorRationalOn k N hN.ne' - labyrinthTargetOn k‖ ≤
      4 * (3 / 4 : ℝ) ^ N := by
  letI : CompactSpace (labyrinthApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro z
  rcases norm_bounds_of_mem_labyrinthApproximationSet z.property with hsmall | hlarge
  · rw [ContinuousMap.sub_apply, labyrinthTargetOn_eq_one z hsmall]
    exact labyrinthSeparatorRational_sub_one_norm_le k hN z hsmall
  · rw [ContinuousMap.sub_apply, labyrinthTargetOn_eq_zero z hlarge.1, sub_zero]
    exact labyrinthSeparatorRational_norm_le k hN z hlarge.1

lemma labyrinthTarget_mem_uniformClosure (k : ℕ) :
    letI : CompactSpace (labyrinthApproximationSet k) :=
      isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
    labyrinthTargetOn k ∈ polynomialUniformClosure (labyrinthApproximationSet k) := by
  letI : CompactSpace (labyrinthApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
  let F : ℕ → C(labyrinthApproximationSet k, ℂ) := fun n ↦
    labyrinthSeparatorRationalOn k (n + 1) (Nat.succ_ne_zero n)
  have hbound : ∀ n,
      ‖F n - labyrinthTargetOn k‖ ≤ 4 * (3 / 4 : ℝ) ^ (n + 1) := by
    intro n
    exact labyrinthSeparatorRational_sub_target_norm_le k (Nat.succ_pos n)
  have hscalar : Tendsto (fun n : ℕ ↦ 4 * (3 / 4 : ℝ) ^ (n + 1)) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ ↦ (3 / 4 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      hp.const_mul (4 * (3 / 4 : ℝ))
  have hnorm : Tendsto (fun n ↦ ‖F n - labyrinthTargetOn k‖) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ norm_nonneg _) hbound hscalar
  have hlim : Tendsto F atTop (𝓝 (labyrinthTargetOn k)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hnorm
  have hclosed : IsClosed
      (polynomialUniformClosure (labyrinthApproximationSet k) :
        Set C(labyrinthApproximationSet k, ℂ)) := by
    unfold polynomialUniformClosure
    exact Subalgebra.isClosed_topologicalClosure _
  apply hclosed.mem_of_tendsto hlim
  filter_upwards [] with n
  exact labyrinthSeparatorRational_mem_uniformClosure k (Nat.succ_ne_zero n)

/-- Normalized polynomial which is close to one on the unit disk and arbitrarily small on the
`k`-gate normalized labyrinth. -/
theorem exists_labyrinthPolynomial (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.eval 0 = 1 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖P.eval z - 1‖ < ε) ∧
      (∀ z ∈ labyrinthSet k 1, ‖P.eval z‖ < ε) := by
  letI : CompactSpace (labyrinthApproximationSet k) :=
    isCompact_iff_compactSpace.mp (isCompact_labyrinthApproximationSet k)
  let δ : ℝ := min (ε / 8) (1 / 8)
  have hδp : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδeight : δ ≤ 1 / 8 := min_le_right _ _
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_mem_uniformClosure
    (labyrinthApproximationSet k) (labyrinthTargetOn k)
      (labyrinthTarget_mem_uniformClosure k) hδp
  have hpoint : ∀ z : labyrinthApproximationSet k,
      ‖q.eval (z : ℂ) - labyrinthTargetOn k z‖ < δ := by
    intro z
    have hzle := ContinuousMap.norm_coe_le_norm
      (q.toContinuousMapOn (labyrinthApproximationSet k) - labyrinthTargetOn k) z
    exact lt_of_le_of_lt (by simpa using hzle) hq
  let z₀ : labyrinthApproximationSet k := ⟨0, by
    left
    simp [labyrinthApproximationSet]⟩
  have htarget0 : labyrinthTargetOn k z₀ = 1 :=
    labyrinthTargetOn_eq_one z₀ (by simp [z₀])
  have hq0 : ‖q.eval 0 - 1‖ < δ := by
    simpa [z₀, htarget0] using hpoint z₀
  have hq0norm : 1 / 2 < ‖q.eval 0‖ := by
    have hrev : 1 - ‖q.eval 0‖ ≤ ‖q.eval 0 - 1‖ := by
      simpa [norm_sub_rev] using norm_sub_norm_le (1 : ℂ) (q.eval 0)
    linarith
  have hq0ne : q.eval 0 ≠ 0 := norm_pos_iff.mp (lt_trans (by norm_num) hq0norm)
  let P : Polynomial ℂ := (q.eval 0)⁻¹ • q
  refine ⟨P, ?_, ?_, ?_⟩
  · simp [P, hq0ne]
  · intro z hz
    let z' : labyrinthApproximationSet k := ⟨z, by
      left
      simpa [labyrinthApproximationSet, Metric.mem_closedBall, Complex.dist_eq] using hz⟩
    have htarget : labyrinthTargetOn k z' = 1 := labyrinthTargetOn_eq_one z' hz
    have hqz : ‖q.eval z - 1‖ < δ := by simpa [z', htarget] using hpoint z'
    have hdiff : ‖q.eval z - q.eval 0‖ < 2 * δ := by
      calc
        ‖q.eval z - q.eval 0‖ = ‖(q.eval z - 1) - (q.eval 0 - 1)‖ := by ring_nf
        _ ≤ ‖q.eval z - 1‖ + ‖q.eval 0 - 1‖ := norm_sub_le _ _
        _ < 2 * δ := by linarith
    have hinv : ‖(q.eval 0)⁻¹‖ < 2 := by
      rw [norm_inv, inv_lt_iff_one_lt_mul₀ (norm_pos_iff.mpr hq0ne)]
      linarith
    have heq : P.eval z - 1 = (q.eval 0)⁻¹ * (q.eval z - q.eval 0) := by
      simp only [P, Polynomial.eval_smul, smul_eq_mul]
      field_simp
    rw [heq, norm_mul]
    have hprod : ‖(q.eval 0)⁻¹‖ * ‖q.eval z - q.eval 0‖ < 2 * (2 * δ) :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hinv.le hdiff (norm_nonneg _) (by norm_num)
    nlinarith
  · intro z hz
    let z' : labyrinthApproximationSet k := ⟨z, Or.inr hz⟩
    have hlarge : 2 ≤ ‖z‖ := by
      simpa using (labyrinthSet_norm_bounds (k := k) (T := 1) (by norm_num) hz).1
    have htarget : labyrinthTargetOn k z' = 0 := labyrinthTargetOn_eq_zero z' hlarge
    have hqz : ‖q.eval z‖ < δ := by simpa [z', htarget] using hpoint z'
    have hinv : ‖(q.eval 0)⁻¹‖ < 2 := by
      rw [norm_inv, inv_lt_iff_one_lt_mul₀ (norm_pos_iff.mpr hq0ne)]
      linarith
    simp only [P, Polynomial.eval_smul, smul_eq_mul, norm_mul]
    have hprod : ‖(q.eval 0)⁻¹‖ * ‖q.eval z‖ < 2 * δ :=
      mul_lt_mul_of_le_of_lt_of_nonneg_of_pos hinv.le hqz (norm_nonneg _) (by norm_num)
    nlinarith

/-- First-hitting-time lemma in the form needed for successive circular gates. -/
lemma exists_first_hitting_time {g : ℝ → ℝ} (hg : Continuous g) {t₀ r : ℝ}
    (h₀ : g t₀ < r) (hevent : Tendsto g atTop atTop) :
    ∃ t : ℝ, t₀ < t ∧ g t = r ∧ ∀ u : ℝ, t₀ ≤ u → u < t → g u < r := by
  obtain ⟨b, hb⟩ := eventually_atTop.1 (hevent.eventually (eventually_ge_atTop r))
  let b' : ℝ := max b t₀
  have ht₀b : t₀ ≤ b' := le_max_right _ _
  have hrb : r ≤ g b' := hb b' (le_max_left _ _)
  have hrmem : r ∈ Set.Icc (g t₀) (g b') := ⟨h₀.le, hrb⟩
  obtain ⟨v, hvIcc, hgv⟩ := intermediate_value_Icc ht₀b hg.continuousOn hrmem
  let A : Set ℝ := Set.Icc t₀ b' ∩ {u | g u = r}
  have hAcompact : IsCompact A :=
    isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hAne : A.Nonempty := ⟨v, hvIcc, hgv⟩
  obtain ⟨t, htA, htleast⟩ := hAcompact.exists_isLeast hAne
  have ht₀t : t₀ ≤ t := htA.1.1
  have hgt : g t = r := htA.2
  have ht₀lt : t₀ < t := lt_of_le_of_ne ht₀t fun heq ↦ by
    subst t
    linarith
  refine ⟨t, ht₀lt, hgt, ?_⟩
  intro u ht₀u hut
  by_contra hnot
  have hrgu : r ≤ g u := le_of_not_gt hnot
  have hru : r ∈ Set.Icc (g t₀) (g u) := ⟨h₀.le, hrgu⟩
  obtain ⟨w, hwIcc, hgw⟩ := intermediate_value_Icc ht₀u hg.continuousOn hru
  have hwA : w ∈ A := ⟨⟨hwIcc.1, le_trans hwIcc.2 hut.le |>.trans htA.1.2⟩, hgw⟩
  exact (not_lt_of_ge (htleast hwA)) (lt_of_le_of_lt hwIcc.2 hut)

lemma volume_timeInDisc_ne_top {γ : ℝ → ℂ}
    (hγ : Tendsto (fun t ↦ ‖γ t‖) atTop atTop) (r : ℝ) :
    volume {t | 0 ≤ t ∧ ‖γ t‖ < r} ≠ ∞ := by
  obtain ⟨B, hB⟩ := eventually_atTop.1 (hγ.eventually (eventually_ge_atTop r))
  have hsubset : {t : ℝ | 0 ≤ t ∧ ‖γ t‖ < r} ⊆ Set.Icc 0 (max B 0) := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    by_contra hnot
    have hBt : B ≤ t := le_trans (le_max_left _ _) (le_of_not_ge hnot)
    exact (not_lt_of_ge (hB t hBt)) ht.2
  exact ne_of_lt (lt_of_le_of_lt (measure_mono hsubset) measure_Icc_lt_top)

/-- Avoiding the alternating gates costs at least `2T` between each consecutive pair. -/
theorem labyrinth_isLengthBarrier (k : ℕ) {T : ℝ} (hT : 0 < T) :
    IsLengthBarrier (labyrinthSet k T) (2 * T) (3 * T)
      (2 * (k - 1 : ℕ) * T) := by
  intro γ hLip hescape t₀ ht₀ hstart havoid
  by_cases hk : k ≤ 1
  · have hkzero : k - 1 = 0 := Nat.sub_eq_zero_of_le hk
    simp [hkzero, lengthInDisc, ENNReal.toReal_nonneg]
  have hk2 : 2 ≤ k := Nat.lt_of_not_ge hk
  have hcont : Continuous (fun t ↦ ‖γ t‖) := hLip.continuous.norm
  have hhits : ∀ i : ℕ, ∃ t : ℝ,
      t₀ < t ∧ ‖γ t‖ = T * gateRadius k i ∧
        ∀ u : ℝ, t₀ ≤ u → u < t → ‖γ u‖ < T * gateRadius k i := by
    intro i
    apply exists_first_hitting_time hcont
    · have : 2 * T ≤ T * gateRadius k i := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left (two_le_gateRadius k i) hT.le
      linarith
    · exact hescape
  choose t ht₀t hnormt hbefore using hhits
  have ht_mono : ∀ {i j : ℕ}, i < j → t i < t j := by
    intro i j hij
    have hradlt : T * gateRadius k i < T * gateRadius k j := by
      have hkpos : 0 < (k + 1 : ℝ) := by positivity
      have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
      simp only [gateRadius]
      apply mul_lt_mul_of_pos_left _ hT
      have := (div_lt_div_iff_of_pos_right hkpos).2 hijR
      linarith
    by_contra hnot
    have hji : t j ≤ t i := le_of_not_gt hnot
    rcases hji.eq_or_lt with heq | hlt
    · have := (hnormt i).symm.trans (heq ▸ hnormt j)
      linarith
    · have hsmall := hbefore i (t j) (ht₀t j).le hlt
      rw [hnormt j] at hsmall
      linarith
  have hsigned : ∀ {i : ℕ}, i < k →
      T < ((-1 : ℝ) ^ i) * (γ (t i)).re := by
    intro i hi
    have hnotgate : γ (t i) ∉ labyrinthGate k i T := by
      intro hgate
      exact havoid (t i) (ht₀t i).le (by
        simp only [labyrinthSet, Set.mem_iUnion]
        exact ⟨i, Finset.mem_range.mpr hi, hgate⟩)
    have hnotle : ¬ ((-1 : ℝ) ^ i) * (γ (t i)).re ≤ T * gateRadius k i / 2 := by
      intro hle
      apply hnotgate
      exact ⟨hnormt i, hle⟩
    have hrad : 2 * T ≤ T * gateRadius k i := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (two_le_gateRadius k i) hT.le
    exact lt_of_le_of_lt (by linarith) (lt_of_not_ge hnotle)
  have hstep : ∀ i : ℕ, i < k - 1 → 2 * T ≤ t (i + 1) - t i := by
    intro i hi
    have hiK : i < k := lt_of_lt_of_le hi (Nat.sub_le k 1)
    have hisK : i + 1 < k := by omega
    have hti : t i < t (i + 1) := ht_mono (Nat.lt_succ_self i)
    have hx := hsigned hiK
    have hy := hsigned hisK
    have hsignsucc : ((-1 : ℝ) ^ (i + 1)) = -((-1 : ℝ) ^ i) := by
      rw [pow_succ]
      ring
    rw [hsignsucc] at hy
    have hreal : 2 * T <
        ((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re) := by
      change 2 * T < ((-1 : ℝ) ^ i) * ((γ (t i)).re - (γ (t (i + 1))).re)
      nlinarith
    have habssign : |((-1 : ℝ) ^ i)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    have habs : 2 * T < |(γ (t i) - γ (t (i + 1))).re| := by
      have hpos : 0 < ((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re) :=
        lt_trans (by positivity) hreal
      calc
        2 * T < |((-1 : ℝ) ^ i) * ((γ (t i) - γ (t (i + 1))).re)| := by
          rwa [abs_of_pos hpos]
        _ = |(γ (t i) - γ (t (i + 1))).re| := by rw [abs_mul, habssign, one_mul]
    have hnorm : 2 * T < ‖γ (t i) - γ (t (i + 1))‖ :=
      lt_of_lt_of_le habs (Complex.abs_re_le_norm _)
    have hdist := hLip.dist_le_mul (t i) (t (i + 1))
    simp only [NNReal.coe_one, one_mul, dist_eq_norm, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr hti.le)] at hdist
    linarith
  have htime : 2 * (k - 1 : ℕ) * T ≤ t (k - 1) - t 0 := by
    calc
      2 * (k - 1 : ℕ) * T = ∑ i ∈ Finset.range (k - 1), (2 * T) := by
        simp
        ring
      _ ≤ ∑ i ∈ Finset.range (k - 1), (t (i + 1) - t i) := by
        exact Finset.sum_le_sum fun i hi ↦ hstep i (Finset.mem_range.mp hi)
      _ = t (k - 1) - t 0 := by
        simpa using Finset.sum_range_sub t (k - 1)
  have hlastK : k - 1 < k := Nat.sub_lt (by omega) (by omega)
  have ht0last : t 0 ≤ t (k - 1) := (ht_mono (by omega)).le
  have hinterval : Set.Icc (t 0) (t (k - 1)) ⊆
      {u : ℝ | 0 ≤ u ∧ ‖γ u‖ < 3 * T} := by
    intro u hu
    refine ⟨le_trans ht₀ (le_trans (ht₀t 0).le hu.1), ?_⟩
    rcases hu.2.eq_or_lt with heq | hlt
    · subst u
      rw [hnormt]
      simpa [mul_comm] using mul_lt_mul_of_pos_left (gateRadius_bounds hlastK).2 hT
    · have hu₀ : t₀ ≤ u := le_trans (ht₀t 0).le hu.1
      have hsmall := hbefore (k - 1) u hu₀ hlt
      exact lt_trans hsmall (by
        simpa [mul_comm] using mul_lt_mul_of_pos_left (gateRadius_bounds hlastK).2 hT)
  have hmeasure : volume (Set.Icc (t 0) (t (k - 1))) ≤
      volume {u : ℝ | 0 ≤ u ∧ ‖γ u‖ < 3 * T} := measure_mono hinterval
  have htoreal := ENNReal.toReal_mono (volume_timeInDisc_ne_top hescape (3 * T)) hmeasure
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr ht0last)] at htoreal
  exact htime.trans (by simpa [lengthInDisc] using htoreal)

/-!
## Polynomial estimates for the inductive product
-/

/-- A coefficient `ℓ¹` bound, enlarged to be at least one. -/
noncomputable def polynomialBound (p : Polynomial ℂ) : ℝ :=
  max 1 (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖)

lemma one_le_polynomialBound (p : Polynomial ℂ) : 1 ≤ polynomialBound p :=
  le_max_left _ _

lemma polynomialBound_pos (p : Polynomial ℂ) : 0 < polynomialBound p :=
  lt_of_lt_of_le zero_lt_one (one_le_polynomialBound p)

lemma polynomial_eval_norm_le (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖ ≤ polynomialBound p * (max 1 ‖z‖) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc
    ‖∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * z ^ i‖ ≤
        ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i * z ^ i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1),
        ‖p.coeff i‖ * (max 1 ‖z‖) ^ p.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      have hiDegree : i ≤ p.natDegree := by
        have := Finset.mem_range.mp hi
        omega
      exact (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) i).trans
        (pow_le_pow_right₀ (le_max_left 1 ‖z‖) hiDegree)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) *
        (max 1 ‖z‖) ^ p.natDegree := by rw [Finset.sum_mul]
    _ ≤ polynomialBound p * (max 1 ‖z‖) ^ p.natDegree := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (pow_nonneg (by positivity) _)

/-- Quotient in `p(z) - p(0) = z * polynomialSlope(p)(z)`. -/
noncomputable def polynomialSlope (p : Polynomial ℂ) : Polynomial ℂ :=
  Classical.choose (Polynomial.X_dvd_sub_C (p := p))

lemma X_mul_polynomialSlope (p : Polynomial ℂ) :
    Polynomial.X * polynomialSlope p = p - Polynomial.C (p.coeff 0) :=
  (Classical.choose_spec (Polynomial.X_dvd_sub_C (p := p))).symm

lemma polynomial_eval_sub_zero_le (p : Polynomial ℂ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖p.eval z - p.eval 0‖ ≤ polynomialBound (polynomialSlope p) * ‖z‖ := by
  have heval : p.eval z - p.eval 0 = z * (polynomialSlope p).eval z := by
    have h := congrArg (fun q : Polynomial ℂ ↦ q.eval z) (X_mul_polynomialSlope p)
    simpa [Polynomial.coeff_zero_eq_eval_zero] using h.symm
  rw [heval, norm_mul]
  have hslope := polynomial_eval_norm_le (polynomialSlope p) z
  rw [max_eq_left (by simpa using hz), one_pow, mul_one] at hslope
  nlinarith [norm_nonneg z]

lemma norm_pow_sub_one_le_exp {a : ℂ} (q : ℕ) :
    ‖a ^ q - 1‖ ≤ Real.exp ((q : ℝ) * ‖a - 1‖) - 1 := by
  let f : ℕ → ℂ := fun _ ↦ a - 1
  have hprod := Finset.norm_prod_one_add_sub_one_le (Finset.range q) f
  simpa [f] using hprod

/-- Fixed normalized separator for the `(n+2)`-gate wall. -/
noncomputable def baseLabyrinthPolynomial (n : ℕ) : Polynomial ℂ :=
  Classical.choose (exists_labyrinthPolynomial (n + 2) (by norm_num : (0 : ℝ) < 1 / 4))

lemma baseLabyrinthPolynomial_zero (n : ℕ) :
    (baseLabyrinthPolynomial n).eval 0 = 1 :=
  (Classical.choose_spec
    (exists_labyrinthPolynomial (n + 2) (by norm_num : (0 : ℝ) < 1 / 4))).1

lemma baseLabyrinthPolynomial_disk (n : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖(baseLabyrinthPolynomial n).eval z - 1‖ < 1 / 4 :=
  (Classical.choose_spec
    (exists_labyrinthPolynomial (n + 2) (by norm_num : (0 : ℝ) < 1 / 4))).2.1 z hz

lemma baseLabyrinthPolynomial_wall (n : ℕ) {z : ℂ}
    (hz : z ∈ labyrinthSet (n + 2) 1) :
    ‖(baseLabyrinthPolynomial n).eval z‖ < 1 / 4 :=
  (Classical.choose_spec
    (exists_labyrinthPolynomial (n + 2) (by norm_num : (0 : ℝ) < 1 / 4))).2.2 z hz

lemma neg_two_mem_labyrinthSet (n : ℕ) :
    ((-2 : ℝ) : ℂ) ∈ labyrinthSet (n + 2) 1 := by
  simp only [labyrinthSet, Set.mem_iUnion]
  refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
  simp [labyrinthGate, gateRadius]
  norm_num

lemma baseLabyrinthPolynomial_natDegree_pos (n : ℕ) :
    0 < (baseLabyrinthPolynomial n).natDegree := by
  apply Nat.pos_of_ne_zero
  intro hdegree
  have hconstant := Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hcoeff : (baseLabyrinthPolynomial n).coeff 0 = 1 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using baseLabyrinthPolynomial_zero n
  have hwall := baseLabyrinthPolynomial_wall n (neg_two_mem_labyrinthSet n)
  rw [hconstant, hcoeff] at hwall
  norm_num at hwall

/-- Error budget for the `n`th factor; its total sum is less than `1/4`. -/
noncomputable def stageError (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n + 3)

lemma stageError_pos (n : ℕ) : 0 < stageError n := by
  exact pow_pos (by norm_num) _

lemma summable_stageError : Summable stageError := by
  have h : Summable (fun n : ℕ ↦ (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (K := ℝ) (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
  have hm : Summable (fun n : ℕ ↦ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n) :=
    h.mul_left (1 / 8 : ℝ)
  exact hm.congr fun n ↦ by
    rw [stageError, pow_add]
    ring

/-- Exponential dilation used at one inductive stage. -/
noncomputable def exponentialScale (A : ℝ) (q : ℕ) : ℝ :=
  Real.exp ((q : ℝ) / A)

lemma tendsto_exponentialScale {A : ℝ} (hA : 0 < A) :
    Tendsto (exponentialScale A) atTop atTop := by
  apply Real.tendsto_exp_atTop.comp
  exact tendsto_natCast_atTop_atTop.atTop_div_const hA

lemma tendsto_nat_mul_inv_exponentialScale {A : ℝ} (hA : 0 < A) :
    Tendsto (fun q : ℕ ↦ (q : ℝ) * (exponentialScale A q)⁻¹) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 A⁻¹ (inv_pos.mpr hA)).comp
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards with q
  simp only [Function.comp_apply, Real.rpow_one, exponentialScale]
  rw [show (Real.exp ((q : ℝ) / A))⁻¹ = Real.exp (-((q : ℝ) / A)) by
    exact (Real.exp_neg _).symm]
  congr 2
  field_simp

/-- The polynomial factor `P(z/T)^q`. -/
noncomputable def scaledPolynomialFactor (p : Polynomial ℂ) (T : ℝ) (q : ℕ) :
    Polynomial ℂ :=
  (p.comp (Polynomial.C ((T⁻¹ : ℝ) : ℂ) * Polynomial.X)) ^ q

lemma scaledPolynomialFactor_eval (p : Polynomial ℂ) (T : ℝ) (q : ℕ) (z : ℂ) :
    (scaledPolynomialFactor p T q).eval z = (p.eval (((T⁻¹ : ℝ) : ℂ) * z)) ^ q := by
  simp [scaledPolynomialFactor]

noncomputable def stageA (Q : Polynomial ℂ) : ℝ :=
  4 * (Q.natDegree + 1 : ℝ)

lemma stageA_pos (Q : Polynomial ℂ) : 0 < stageA Q := by
  simp [stageA]
  positivity

lemma stage_degree_div_A_le (Q : Polynomial ℂ) :
    (Q.natDegree : ℝ) / stageA Q ≤ 1 / 4 := by
  rw [div_le_iff₀ (stageA_pos Q)]
  simp only [stageA]
  have hD : 0 ≤ (Q.natDegree : ℝ) := by positivity
  nlinarith

lemma stage_wall_ratio_lt_one (Q : Polynomial ℂ) :
    Real.exp ((Q.natDegree : ℝ) / stageA Q) / 4 < 1 := by
  have harg : (Q.natDegree : ℝ) / stageA Q < 1 :=
    lt_of_le_of_lt (stage_degree_div_A_le Q) (by norm_num)
  have hexp : Real.exp ((Q.natDegree : ℝ) / stageA Q) < 3 :=
    (Real.exp_lt_exp.mpr harg).trans Real.exp_one_lt_three
  nlinarith

lemma tendsto_stage_wall_bound (Q : Polynomial ℂ) :
    Tendsto (fun q : ℕ ↦
      polynomialBound Q * (3 * exponentialScale (stageA Q) q) ^ Q.natDegree *
        (1 / 4 : ℝ) ^ q) atTop (𝓝 0) := by
  let b : ℝ := Real.exp ((Q.natDegree : ℝ) / stageA Q) / 4
  have hb0 : 0 ≤ b := by positivity
  have hb1 : b < 1 := stage_wall_ratio_lt_one Q
  have hpow : Tendsto (fun q : ℕ ↦ b ^ q) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1
  have hconst := hpow.const_mul (polynomialBound Q * (3 : ℝ) ^ Q.natDegree)
  convert hconst using 1
  funext q
  simp only [b, exponentialScale]
  have hleft : Real.exp ((q : ℝ) / stageA Q) ^ Q.natDegree =
      Real.exp ((Q.natDegree : ℝ) * ((q : ℝ) / stageA Q)) := by
    rw [Real.exp_nat_mul]
  have hright : Real.exp ((Q.natDegree : ℝ) / stageA Q) ^ q =
      Real.exp ((q : ℝ) * ((Q.natDegree : ℝ) / stageA Q)) := by
    rw [Real.exp_nat_mul]
  rw [mul_pow, hleft]
  simp_rw [div_pow]
  rw [one_pow, hright]
  have hfour : (4 : ℝ) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hfour]
  congr 2 <;> field_simp [stageA_pos Q |>.ne'] <;> ring

noncomputable def stageGrowthConstant (Q p : Polynomial ℂ) : ℝ :=
  Real.log (polynomialBound Q) + Q.natDegree +
    stageA Q * Real.log (polynomialBound p) + stageA Q * p.natDegree

lemma stageGrowthConstant_nonneg (Q p : Polynomial ℂ) :
    0 ≤ stageGrowthConstant Q p := by
  have hlogQ : 0 ≤ Real.log (polynomialBound Q) :=
    Real.log_nonneg (one_le_polynomialBound Q)
  have hlogp : 0 ≤ Real.log (polynomialBound p) :=
    Real.log_nonneg (one_le_polynomialBound p)
  have hA : 0 ≤ stageA Q := (stageA_pos Q).le
  have hDQ : 0 ≤ (Q.natDegree : ℝ) := by positivity
  have hDp : 0 ≤ (p.natDegree : ℝ) := by positivity
  simp only [stageGrowthConstant]
  exact add_nonneg (add_nonneg (add_nonneg hlogQ hDQ) (mul_nonneg hA hlogp))
    (mul_nonneg hA hDp)

/-- The logarithmic error budget used to locate the radius at which a new factor becomes active. -/
noncomputable def stageDelta (n : ℕ) : ℝ := Real.log (1 + stageError n)

lemma stageDelta_pos (n : ℕ) : 0 < stageDelta n := by
  rw [stageDelta]
  exact Real.log_pos (by linarith [stageError_pos n])

lemma stageDelta_lt_one (n : ℕ) : stageDelta n < 1 := by
  have herr : stageError n ≤ 1 / 8 := by
    rw [stageError, show n + 3 = 3 + n by omega, pow_add]
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    norm_num
    nlinarith
  have harg : 1 + stageError n < Real.exp 1 := by
    nlinarith [Real.exp_one_gt_two]
  have hlog := Real.strictMonoOn_log
    (show 0 < 1 + stageError n by linarith [stageError_pos n]) (Real.exp_pos 1) harg
  simpa [stageDelta] using hlog

/-- Up to this radius the new factor differs from one by at most its allotted error. -/
noncomputable def stageActivation (Q : Polynomial ℂ) (n q : ℕ) : ℝ :=
  stageDelta n * exponentialScale (stageA Q) q /
    (((q + 1 : ℕ) : ℝ) * polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)))

lemma stageActivation_pos (Q : Polynomial ℂ) (n q : ℕ) :
    0 < stageActivation Q n q := by
  unfold stageActivation
  exact div_pos (mul_pos (stageDelta_pos n) (Real.exp_pos _))
    (mul_pos (by exact_mod_cast Nat.succ_pos q) (polynomialBound_pos _))

lemma stageActivation_lt_scale (Q : Polynomial ℂ) (n q : ℕ) :
    stageActivation Q n q < exponentialScale (stageA Q) q := by
  have hδ := stageDelta_lt_one n
  have hden : 1 ≤ ((q + 1 : ℕ) : ℝ) *
      polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) := by
    have hq : (1 : ℝ) ≤ (q + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
    exact one_le_mul_of_one_le_of_one_le hq (one_le_polynomialBound _)
  have hscale := Real.exp_pos ((q : ℝ) / stageA Q)
  unfold stageActivation exponentialScale
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith

lemma tendsto_stageActivation (Q : Polynomial ℂ) (n : ℕ) :
    Tendsto (stageActivation Q n) atTop atTop := by
  let T : ℕ → ℝ := exponentialScale (stageA Q)
  let u : ℕ → ℝ := fun q ↦ ((q + 1 : ℕ) : ℝ) * (T q)⁻¹
  have hT : Tendsto T atTop atTop := tendsto_exponentialScale (stageA_pos Q)
  have hqT : Tendsto (fun q : ℕ ↦ (q : ℝ) * (T q)⁻¹) atTop (𝓝 0) :=
    tendsto_nat_mul_inv_exponentialScale (stageA_pos Q)
  have hinvT : Tendsto (fun q : ℕ ↦ (T q)⁻¹) atTop (𝓝 0) := hT.inv_tendsto_atTop
  have hu : Tendsto u atTop (𝓝 0) := by
    have hadd := hqT.add hinvT
    simp only [zero_add] at hadd
    apply hadd.congr'
    filter_upwards with q
    simp only [u]
    push_cast
    ring
  have hupos : ∀ᶠ q : ℕ in atTop, 0 < u q := by
    filter_upwards with q
    unfold u T
    exact mul_pos (by exact_mod_cast Nat.succ_pos q) (inv_pos.mpr (Real.exp_pos _))
  have huWithin : Tendsto u atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, hupos⟩
  have huinv : Tendsto (fun q ↦ (u q)⁻¹) atTop atTop :=
    huWithin.inv_tendsto_nhdsGT_zero
  have hc : 0 < stageDelta n /
      polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) := div_pos
        (stageDelta_pos n) (polynomialBound_pos _)
  have hmul := Filter.Tendsto.const_mul_atTop hc huinv
  apply hmul.congr'
  filter_upwards with q
  unfold stageActivation u T
  have hq : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hscale : 0 < exponentialScale (stageA Q) q := Real.exp_pos _
  field_simp

lemma eventually_nat_le_two_stageA_log_activation (Q : Polynomial ℂ) (n : ℕ) :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) ≤ 2 * stageA Q * Real.log (stageActivation Q n q) := by
  let A := stageA Q
  let B := polynomialBound (polynomialSlope (baseLabyrinthPolynomial n))
  let δ := stageDelta n
  have hA : 0 < A := stageA_pos Q
  have hdec0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (2 * A)⁻¹
    (by positivity : 0 < (2 * A)⁻¹)).comp tendsto_natCast_atTop_atTop
  have hdec0' : Tendsto (fun q : ℕ ↦
      (q : ℝ) * Real.exp (-((q : ℝ) / (2 * A)))) atTop (𝓝 0) := by
    apply hdec0.congr'
    filter_upwards with q
    simp only [Function.comp_apply, Real.rpow_one]
    congr 2
    field_simp [hA.ne']
  have hdec : Tendsto (fun q : ℕ ↦
      ((q + 1 : ℕ) : ℝ) * Real.exp (-((q : ℝ) / (2 * A)))) atTop (𝓝 0) := by
    have hexp : Tendsto (fun q : ℕ ↦ Real.exp (-((q : ℝ) / (2 * A)))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun q : ℕ ↦ (q : ℝ) / (2 * A)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_div_const (by positivity)
      simpa only [Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
    have hadd := hdec0'.add hexp
    simp only [zero_add] at hadd
    apply hadd.congr'
    filter_upwards with q
    push_cast
    ring
  have hc : 0 < B / δ := div_pos (polynomialBound_pos _) (stageDelta_pos n)
  have hratio : Tendsto (fun q : ℕ ↦
      (B / δ) * (((q + 1 : ℕ) : ℝ) * Real.exp (-((q : ℝ) / (2 * A)))))
      atTop (𝓝 0) := by simpa using hdec.const_mul (B / δ)
  have hle : ∀ᶠ q : ℕ in atTop,
      (B / δ) * (((q + 1 : ℕ) : ℝ) * Real.exp (-((q : ℝ) / (2 * A)))) ≤ 1 :=
    hratio.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hle] with q hq
  have hRpos := stageActivation_pos Q n q
  have hExpR : Real.exp ((q : ℝ) / (2 * A)) ≤ stageActivation Q n q := by
    have hδ : 0 < δ := stageDelta_pos n
    have hB : 0 < B := polynomialBound_pos _
    have hq1 : (0 : ℝ) < (q + 1 : ℕ) := by positivity
    have he : 0 < Real.exp ((q : ℝ) / (2 * A)) := Real.exp_pos _
    have hexpadd : Real.exp ((q : ℝ) / A) =
        Real.exp ((q : ℝ) / (2 * A)) * Real.exp ((q : ℝ) / (2 * A)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hA.ne']
      ring
    have hbase : B * ((q + 1 : ℕ) : ℝ) ≤
        δ * Real.exp ((q : ℝ) / (2 * A)) := by
      rw [Real.exp_neg] at hq
      calc
        B * ((q + 1 : ℕ) : ℝ) =
            ((B / δ) * (((q + 1 : ℕ) : ℝ) *
              (Real.exp ((q : ℝ) / (2 * A)))⁻¹)) *
                (δ * Real.exp ((q : ℝ) / (2 * A))) := by
          field_simp [hδ.ne', he.ne']
        _ ≤ 1 * (δ * Real.exp ((q : ℝ) / (2 * A))) :=
          mul_le_mul_of_nonneg_right hq (mul_nonneg hδ.le he.le)
        _ = _ := one_mul _
    unfold stageActivation exponentialScale
    dsimp only [A, B, δ] at hexpadd hbase ⊢
    rw [hexpadd]
    apply (le_div_iff₀ (mul_pos hq1 hB)).2
    have hm := mul_le_mul_of_nonneg_right hbase he.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm
  have hlog := Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hRpos hExpR
  rw [Real.log_exp] at hlog
  dsimp only [A] at hlog ⊢
  have := (div_le_iff₀ (by positivity : 0 < 2 * stageA Q)).mp hlog
  simpa [mul_assoc, mul_left_comm, mul_comm] using this

lemma stageActivation_near_bound (Q : Polynomial ℂ) (n q : ℕ) :
    Real.exp ((q : ℝ) * polynomialBound
      (polynomialSlope (baseLabyrinthPolynomial n)) * stageActivation Q n q *
        (exponentialScale (stageA Q) q)⁻¹) - 1 ≤ stageError n := by
  let B := polynomialBound (polynomialSlope (baseLabyrinthPolynomial n))
  let T := exponentialScale (stageA Q) q
  have hB : 0 < B := polynomialBound_pos _
  have hT : 0 < T := Real.exp_pos _
  have hq1 : (0 : ℝ) < (q + 1 : ℕ) := by positivity
  have hfrac : (q : ℝ) / (q + 1 : ℕ) ≤ 1 := by
    apply (div_le_one hq1).2
    norm_num
  have harg : (q : ℝ) * B * stageActivation Q n q * T⁻¹ ≤ stageDelta n := by
    have hδ := (stageDelta_pos n).le
    have heq : (q : ℝ) * B * stageActivation Q n q * T⁻¹ =
        ((q : ℝ) / (q + 1 : ℕ)) * stageDelta n := by
      unfold stageActivation
      dsimp only [B, T]
      dsimp only [B, T] at hB hT
      field_simp [hB.ne', hT.ne', hq1.ne']
    rw [heq]
    exact mul_le_of_le_one_left hδ hfrac
  calc
    _ ≤ Real.exp (stageDelta n) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr harg) 1
    _ = stageError n := by
      rw [stageDelta, Real.exp_log (by linarith [stageError_pos n])]
      ring

/-- All numerical requirements at one inductive step can be met by a sufficiently large integer
multiplicity. -/
lemma exists_stage_exponent (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (Q : Polynomial ℂ) (n : ℕ) {lastT : ℝ} (hlastT : 0 ≤ lastT) :
    ∃ q : ℕ, 0 < q ∧
      Real.exp 1 < exponentialScale (stageA Q) q ∧
      3 * lastT < exponentialScale (stageA Q) q ∧
      (∀ r ≥ exponentialScale (stageA Q) q,
        stageGrowthConstant Q (baseLabyrinthPolynomial n) + 1 ≤ φ r) ∧
      polynomialBound Q * (3 * exponentialScale (stageA Q) q) ^ Q.natDegree *
        (1 / 4 : ℝ) ^ q ≤ 1 / 4 ∧
      Real.exp ((q : ℝ) * polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * lastT) *
          (exponentialScale (stageA Q) q)⁻¹) - 1 ≤ stageError n ∧
      Real.exp 1 < stageActivation Q n q ∧
      3 * lastT < stageActivation Q n q ∧
      (∀ r ≥ stageActivation Q n q,
        2 * stageGrowthConstant Q (baseLabyrinthPolynomial n) + 1 ≤ φ r) ∧
      (q : ℝ) ≤ 2 * stageA Q * Real.log (stageActivation Q n q) ∧
      Real.exp ((q : ℝ) * polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * stageActivation Q n q *
          (exponentialScale (stageA Q) q)⁻¹) - 1 ≤ stageError n := by
  let C := stageGrowthConstant Q (baseLabyrinthPolynomial n)
  obtain ⟨R, hR⟩ := eventually_atTop.1
    (hφ.eventually (eventually_ge_atTop (2 * C + 1)))
  have hactivation := tendsto_stageActivation Q n
  have hlarge : ∀ᶠ q : ℕ in atTop,
      Real.exp 1 < stageActivation Q n q ∧
      3 * lastT < stageActivation Q n q ∧
      R ≤ stageActivation Q n q := by
    filter_upwards
      [hactivation.eventually (eventually_gt_atTop (Real.exp 1)),
       hactivation.eventually (eventually_gt_atTop (3 * lastT)),
       hactivation.eventually (eventually_ge_atTop R)] with q hq1 hq2 hqR
    exact ⟨hq1, hq2, hqR⟩
  have hwall : ∀ᶠ q : ℕ in atTop,
      polynomialBound Q * (3 * exponentialScale (stageA Q) q) ^ Q.natDegree *
        (1 / 4 : ℝ) ^ q ≤ 1 / 4 := by
    exact (tendsto_stage_wall_bound Q).eventually
      (show Set.Iic (1 / 4 : ℝ) ∈ 𝓝 0 by exact Iic_mem_nhds (by norm_num))
  let K : ℝ := polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * lastT)
  have hscalar : Tendsto
      (fun q : ℕ ↦ K * ((q : ℝ) * (exponentialScale (stageA Q) q)⁻¹))
      atTop (𝓝 0) := by
    simpa using (tendsto_nat_mul_inv_exponentialScale (stageA_pos Q)).const_mul K
  have hnear0 : Tendsto (fun q : ℕ ↦
      Real.exp ((q : ℝ) * polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * lastT) *
          (exponentialScale (stageA Q) q)⁻¹) - 1) atTop (𝓝 0) := by
    have hexp : Tendsto (fun q : ℕ ↦ Real.exp
        (K * ((q : ℝ) * (exponentialScale (stageA Q) q)⁻¹))) atTop (𝓝 1) := by
      have hc := (Real.continuous_exp.tendsto 0).comp hscalar
      rw [Real.exp_zero] at hc
      exact hc.congr' (by filter_upwards with q; rfl)
    have hsub : Tendsto (fun q : ℕ ↦
        Real.exp (K * ((q : ℝ) * (exponentialScale (stageA Q) q)⁻¹)) - 1)
        atTop (𝓝 0) := by simpa using hexp.sub_const 1
    apply hsub.congr'
    filter_upwards with q
    simp only [K]
    congr 2
    ring
  have hnear : ∀ᶠ q : ℕ in atTop,
      Real.exp ((q : ℝ) * polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * lastT) *
          (exponentialScale (stageA Q) q)⁻¹) - 1 ≤ stageError n :=
    hnear0.eventually (Iic_mem_nhds (stageError_pos n))
  have hqlog := eventually_nat_le_two_stageA_log_activation Q n
  have hqpos : ∀ᶠ q : ℕ in atTop, 0 < q := eventually_gt_atTop 0
  obtain ⟨q, hq, hqL, hqW, hqN, hqlog'⟩ :=
    (hqpos.and (hlarge.and (hwall.and (hnear.and hqlog)))).exists
  have hactlt := stageActivation_lt_scale Q n q
  refine ⟨q, hq, hqL.1.trans hactlt, hqL.2.1.trans hactlt, ?_, hqW, hqN,
    hqL.1, hqL.2.1, ?_, hqlog', stageActivation_near_bound Q n q⟩
  · intro r hr
    have hstrong := hR r (le_trans hqL.2.2 (le_trans hactlt.le hr))
    have hC : 0 ≤ C := stageGrowthConstant_nonneg _ _
    dsimp only [C] at hstrong ⊢
    linarith
  · intro r hr
    exact hR r (le_trans hqL.2.2 hr)

structure ProductStage where
  Q : Polynomial ℂ
  T : ℝ
  q : ℕ
  C : ℝ
  T_pos : 0 < T

noncomputable def initialProductStage : ProductStage where
  Q := 1
  T := 1
  q := 0
  C := 0
  T_pos := zero_lt_one

noncomputable def nextProductStage (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) : ProductStage := by
  let q := Classical.choose (exists_stage_exponent φ hφ prev.Q n prev.T_pos.le)
  let T := exponentialScale (stageA prev.Q) q
  exact
    { Q := prev.Q * scaledPolynomialFactor (baseLabyrinthPolynomial n) T q
      T := T
      q := q
      C := stageGrowthConstant prev.Q (baseLabyrinthPolynomial n)
      T_pos := Real.exp_pos _ }

lemma nextProductStage_spec (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) :
    let next := nextProductStage φ hφ n prev
    0 < next.q ∧
    Real.exp 1 < next.T ∧
    3 * prev.T < next.T ∧
    (∀ r ≥ next.T, next.C + 1 ≤ φ r) ∧
    polynomialBound prev.Q * (3 * next.T) ^ prev.Q.natDegree *
      (1 / 4 : ℝ) ^ next.q ≤ 1 / 4 ∧
    Real.exp ((next.q : ℝ) * polynomialBound
      (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * prev.T) * next.T⁻¹) - 1 ≤
        stageError n := by
  have h := Classical.choose_spec (exists_stage_exponent φ hφ prev.Q n prev.T_pos.le)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

lemma nextProductStage_activation_spec (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) :
    let next := nextProductStage φ hφ n prev
    let R := stageActivation prev.Q n next.q
    Real.exp 1 < R ∧
    3 * prev.T < R ∧
    (∀ r ≥ R, 2 * next.C + 1 ≤ φ r) ∧
    (next.q : ℝ) ≤ 2 * stageA prev.Q * Real.log R ∧
    Real.exp ((next.q : ℝ) * polynomialBound
      (polynomialSlope (baseLabyrinthPolynomial n)) * R * next.T⁻¹) - 1 ≤
        stageError n := by
  have h := Classical.choose_spec (exists_stage_exponent φ hφ prev.Q n prev.T_pos.le)
  exact h.2.2.2.2.2.2

lemma nextProductStage_Q (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) :
    (nextProductStage φ hφ n prev).Q = prev.Q *
      scaledPolynomialFactor (baseLabyrinthPolynomial n)
        (nextProductStage φ hφ n prev).T (nextProductStage φ hφ n prev).q := rfl

lemma nextProductStage_T (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) :
    (nextProductStage φ hφ n prev).T =
      exponentialScale (stageA prev.Q) (nextProductStage φ hφ n prev).q := rfl

lemma nextProductStage_factor_close (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) {z : ℂ} (hz : ‖z‖ ≤ 3 * prev.T) :
    ‖(scaledPolynomialFactor (baseLabyrinthPolynomial n)
        (nextProductStage φ hφ n prev).T (nextProductStage φ hφ n prev).q).eval z - 1‖ ≤
      stageError n := by
  let next := nextProductStage φ hφ n prev
  have hspec := nextProductStage_spec φ hφ n prev
  have hTpos : 0 < next.T := next.T_pos
  have hprev : 0 < prev.T := prev.T_pos
  have hw : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    rw [← div_eq_inv_mul]
    exact (div_le_one hTpos).2 (hz.trans (hspec.2.2.1.le))
  have hbase := polynomial_eval_sub_zero_le (baseLabyrinthPolynomial n) hw
  rw [baseLabyrinthPolynomial_zero] at hbase
  have hpow := norm_pow_sub_one_le_exp
    (a := (baseLabyrinthPolynomial n).eval (((next.T⁻¹ : ℝ) : ℂ) * z)) next.q
  rw [scaledPolynomialFactor_eval]
  refine hpow.trans (le_trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1) hspec.2.2.2.2.2)
  have hnormz : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ 3 * prev.T * next.T⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    calc
      next.T⁻¹ * ‖z‖ ≤ next.T⁻¹ * (3 * prev.T) :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hTpos.le)
      _ = 3 * prev.T * next.T⁻¹ := by ring
  have hq0 : 0 ≤ (next.q : ℝ) := by positivity
  change (next.q : ℝ) *
      ‖(baseLabyrinthPolynomial n).eval (((next.T⁻¹ : ℝ) : ℂ) * z) - 1‖ ≤
    (next.q : ℝ) * polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) *
      (3 * prev.T) * next.T⁻¹
  calc
    _ ≤ (next.q : ℝ) * (polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * (3 * prev.T * next.T⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (hbase.trans (mul_le_mul_of_nonneg_left hnormz
          (polynomialBound_pos _).le)) hq0
    _ = _ := by ring

lemma inv_smul_mem_labyrinthSet {k : ℕ} {T : ℝ} (hT : 0 < T) {z : ℂ}
    (hz : z ∈ labyrinthSet k T) :
    (((T⁻¹ : ℝ) : ℂ) * z) ∈ labyrinthSet k 1 := by
  simp only [labyrinthSet, Set.mem_iUnion] at hz ⊢
  obtain ⟨i, hi, hgate⟩ := hz
  refine ⟨i, hi, ?_⟩
  constructor
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hT,
      hgate.1]
    field_simp [hT.ne']
  · simp only [one_mul]
    change ((-1 : ℝ) ^ i) * ((((T⁻¹ : ℝ) : ℂ) * z).re) ≤ gateRadius k i / 2
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hinv := mul_le_mul_of_nonneg_left hgate.2 (inv_nonneg.mpr hT.le)
    field_simp [hT.ne'] at hinv ⊢
    nlinarith

lemma nextProductStage_wall (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) {z : ℂ}
    (hz : z ∈ labyrinthSet (n + 2) (nextProductStage φ hφ n prev).T) :
    ‖(nextProductStage φ hφ n prev).Q.eval z‖ ≤ 1 / 4 := by
  let next := nextProductStage φ hφ n prev
  have hspec := nextProductStage_spec φ hφ n prev
  have hTpos : 0 < next.T := next.T_pos
  have hnorm := labyrinthSet_norm_bounds hTpos hz
  have hT1 : 1 < next.T := lt_trans (lt_trans (by norm_num) Real.exp_one_gt_two) hspec.2.1
  have hmax : max 1 ‖z‖ ≤ 3 * next.T := by
    apply max_le
    · nlinarith
    · exact hnorm.2.le
  have hQ := polynomial_eval_norm_le prev.Q z
  have hQ' : ‖prev.Q.eval z‖ ≤
      polynomialBound prev.Q * (3 * next.T) ^ prev.Q.natDegree :=
    hQ.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmax _) (polynomialBound_pos _).le)
  have hw := inv_smul_mem_labyrinthSet hTpos hz
  have hp := baseLabyrinthPolynomial_wall n hw
  have hfactor : ‖(scaledPolynomialFactor (baseLabyrinthPolynomial n) next.T next.q).eval z‖ ≤
      (1 / 4 : ℝ) ^ next.q := by
    rw [scaledPolynomialFactor_eval, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp.le _
  rw [nextProductStage_Q, Polynomial.eval_mul, norm_mul]
  calc
    ‖prev.Q.eval z‖ *
        ‖(scaledPolynomialFactor (baseLabyrinthPolynomial n) next.T next.q).eval z‖ ≤
      (polynomialBound prev.Q * (3 * next.T) ^ prev.Q.natDegree) *
        ‖(scaledPolynomialFactor (baseLabyrinthPolynomial n) next.T next.q).eval z‖ :=
      mul_le_mul_of_nonneg_right hQ' (norm_nonneg _)
    _ ≤ (polynomialBound prev.Q * (3 * next.T) ^ prev.Q.natDegree) *
        (1 / 4 : ℝ) ^ next.q :=
      mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg (polynomialBound_pos _).le (pow_nonneg (by positivity) _))
    _ ≤ 1 / 4 := hspec.2.2.2.2.1

lemma nextProductStage_growth (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) (prev : ProductStage) {r : ℝ}
    (hr : (nextProductStage φ hφ n prev).T ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(nextProductStage φ hφ n prev).Q.eval z‖ ≤
      Real.exp ((nextProductStage φ hφ n prev).C * (Real.log r) ^ 2) := by
  let next := nextProductStage φ hφ n prev
  let p := baseLabyrinthPolynomial n
  let A := stageA prev.Q
  let x := Real.log r
  have hspec := nextProductStage_spec φ hφ n prev
  have hTpos : 0 < next.T := next.T_pos
  have hT1 : 1 < next.T :=
    lt_trans (lt_trans (by norm_num) Real.exp_one_gt_two) hspec.2.1
  have hr1 : 1 < r := lt_of_lt_of_le hT1 hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have hlogTle : Real.log next.T ≤ x :=
    Real.strictMonoOn_log.monotoneOn hTpos hrpos hr
  have hx1 : 1 ≤ x := by
    have hlogT : 1 < Real.log next.T := by
      rw [nextProductStage_T, exponentialScale, Real.log_exp]
      have hqA : stageA prev.Q < (next.q : ℝ) := by
        have hscale := hspec.2.1
        rw [nextProductStage_T, exponentialScale, Real.exp_lt_exp] at hscale
        change stageA prev.Q < ((nextProductStage φ hφ n prev).q : ℝ)
        simpa only [one_mul] using (lt_div_iff₀ (stageA_pos prev.Q)).mp hscale
      apply (lt_div_iff₀ (stageA_pos prev.Q)).2
      simpa only [one_mul] using hqA
    exact (hlogT.trans_le hlogTle).le
  have hqeq : (next.q : ℝ) = A * Real.log next.T := by
    change ((nextProductStage φ hφ n prev).q : ℝ) =
      A * Real.log (nextProductStage φ hφ n prev).T
    rw [nextProductStage_T, exponentialScale, Real.log_exp]
    dsimp [A]
    field_simp [stageA_pos prev.Q |>.ne']
  have hqle : (next.q : ℝ) ≤ A * x := by
    rw [hqeq]
    exact mul_le_mul_of_nonneg_left hlogTle (stageA_pos prev.Q).le
  have hmaxz : max 1 ‖z‖ ≤ r := max_le hr1.le hz
  have hQ := polynomial_eval_norm_le prev.Q z
  have hQ' : ‖prev.Q.eval z‖ ≤ polynomialBound prev.Q * r ^ prev.Q.natDegree :=
    hQ.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmaxz _) (polynomialBound_pos _).le)
  have hinvT : next.T⁻¹ ≤ 1 := (inv_le_one₀ hTpos).2 hT1.le
  have hw : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    calc
      next.T⁻¹ * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right hinvT (norm_nonneg z)
      _ ≤ r := by simpa using hz
  have hmaxw : max 1 ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ r := max_le hr1.le hw
  have hp := polynomial_eval_norm_le p (((next.T⁻¹ : ℝ) : ℂ) * z)
  have hp' : ‖p.eval (((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤
      polynomialBound p * r ^ p.natDegree :=
    hp.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmaxw _) (polynomialBound_pos _).le)
  have hfactor : ‖(scaledPolynomialFactor p next.T next.q).eval z‖ ≤
      (polynomialBound p * r ^ p.natDegree) ^ next.q := by
    rw [scaledPolynomialFactor_eval, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp' _
  have hraw : ‖next.Q.eval z‖ ≤
      polynomialBound prev.Q * r ^ prev.Q.natDegree *
        (polynomialBound p * r ^ p.natDegree) ^ next.q := by
    rw [nextProductStage_Q, Polynomial.eval_mul, norm_mul]
    exact mul_le_mul hQ' hfactor (norm_nonneg _)
      (mul_nonneg (polynomialBound_pos _).le (pow_nonneg hrpos.le _))
  let E : ℝ := Real.log (polynomialBound prev.Q) + (prev.Q.natDegree : ℝ) * x +
    (next.q : ℝ) * Real.log (polynomialBound p) +
      (next.q : ℝ) * (p.natDegree : ℝ) * x
  have hUeq : polynomialBound prev.Q * r ^ prev.Q.natDegree *
        (polynomialBound p * r ^ p.natDegree) ^ next.q = Real.exp E := by
    have hBQ : polynomialBound prev.Q = Real.exp (Real.log (polynomialBound prev.Q)) :=
      (Real.exp_log (polynomialBound_pos prev.Q)).symm
    have hBp : polynomialBound p = Real.exp (Real.log (polynomialBound p)) :=
      (Real.exp_log (polynomialBound_pos p)).symm
    have hrE : r = Real.exp x := by
      exact (Real.exp_log hrpos).symm
    rw [hBQ, hBp, hrE]
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [E]
    push_cast
    ring
  have hlQ : 0 ≤ Real.log (polynomialBound prev.Q) :=
    Real.log_nonneg (one_le_polynomialBound prev.Q)
  have hlp : 0 ≤ Real.log (polynomialBound p) :=
    Real.log_nonneg (one_le_polynomialBound p)
  have hA : 0 ≤ A := (stageA_pos prev.Q).le
  have hD : 0 ≤ (prev.Q.natDegree : ℝ) := by positivity
  have hd : 0 ≤ (p.natDegree : ℝ) := by positivity
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hterm1 : Real.log (polynomialBound prev.Q) ≤
      Real.log (polynomialBound prev.Q) * x ^ 2 := by nlinarith
  have hterm2 : (prev.Q.natDegree : ℝ) * x ≤
      (prev.Q.natDegree : ℝ) * x ^ 2 :=
    mul_le_mul_of_nonneg_left hxx hD
  have hterm3 : (next.q : ℝ) * Real.log (polynomialBound p) ≤
      (A * Real.log (polynomialBound p)) * x ^ 2 := by
    calc
      _ ≤ (A * x) * Real.log (polynomialBound p) :=
        mul_le_mul_of_nonneg_right hqle hlp
      _ ≤ (A * Real.log (polynomialBound p)) * x ^ 2 := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hxx (mul_nonneg hA hlp)
  have hterm4 : (next.q : ℝ) * (p.natDegree : ℝ) * x ≤
      (A * (p.natDegree : ℝ)) * x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hqle (mul_nonneg hd hx0)
    nlinarith
  have hEle : E ≤ next.C * x ^ 2 := by
    have hC : next.C = stageGrowthConstant prev.Q p := rfl
    rw [hC]
    simp only [stageGrowthConstant, E]
    nlinarith
  exact hraw.trans (by rw [hUeq]; exact Real.exp_le_exp.mpr hEle)

lemma nextProductStage_growth_from_activation (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) (n : ℕ) (prev : ProductStage) {r : ℝ}
    (hr : stageActivation prev.Q n (nextProductStage φ hφ n prev).q ≤ r)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(nextProductStage φ hφ n prev).Q.eval z‖ ≤
      Real.exp (2 * (nextProductStage φ hφ n prev).C * (Real.log r) ^ 2) := by
  let next := nextProductStage φ hφ n prev
  let p := baseLabyrinthPolynomial n
  let A := stageA prev.Q
  let x := Real.log r
  let R := stageActivation prev.Q n next.q
  have hspec := nextProductStage_spec φ hφ n prev
  have hact := nextProductStage_activation_spec φ hφ n prev
  have hTpos : 0 < next.T := next.T_pos
  have hT1 : 1 < next.T :=
    lt_trans (lt_trans (by norm_num) Real.exp_one_gt_two) hspec.2.1
  have hR1 : 1 < R :=
    (lt_trans (by norm_num) Real.exp_one_gt_two).trans hact.1
  have hr1 : 1 < r := hR1.trans_le hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr1
  have hRpos : 0 < R := lt_trans zero_lt_one hR1
  have hlogRle : Real.log R ≤ x :=
    Real.strictMonoOn_log.monotoneOn hRpos hrpos hr
  have hx1 : 1 ≤ x := by
    have hlogR : 1 < Real.log R := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log (Real.exp_pos 1) hRpos hact.1
    exact (hlogR.trans_le hlogRle).le
  have hqle : (next.q : ℝ) ≤ 2 * A * x := by
    calc
      _ ≤ 2 * stageA prev.Q * Real.log R := hact.2.2.2.1
      _ ≤ 2 * A * x := by
        dsimp only [A]
        exact mul_le_mul_of_nonneg_left hlogRle
          (mul_nonneg (by norm_num) (stageA_pos prev.Q).le)
  have hmaxz : max 1 ‖z‖ ≤ r := max_le hr1.le hz
  have hQ := polynomial_eval_norm_le prev.Q z
  have hQ' : ‖prev.Q.eval z‖ ≤ polynomialBound prev.Q * r ^ prev.Q.natDegree :=
    hQ.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmaxz _) (polynomialBound_pos _).le)
  have hinvT : next.T⁻¹ ≤ 1 := (inv_le_one₀ hTpos).2 hT1.le
  have hw : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    calc
      next.T⁻¹ * ‖z‖ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right hinvT (norm_nonneg z)
      _ ≤ r := by simpa using hz
  have hmaxw : max 1 ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ r := max_le hr1.le hw
  have hp := polynomial_eval_norm_le p (((next.T⁻¹ : ℝ) : ℂ) * z)
  have hp' : ‖p.eval (((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤
      polynomialBound p * r ^ p.natDegree :=
    hp.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hmaxw _) (polynomialBound_pos _).le)
  have hfactor : ‖(scaledPolynomialFactor p next.T next.q).eval z‖ ≤
      (polynomialBound p * r ^ p.natDegree) ^ next.q := by
    rw [scaledPolynomialFactor_eval, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hp' _
  have hraw : ‖next.Q.eval z‖ ≤
      polynomialBound prev.Q * r ^ prev.Q.natDegree *
        (polynomialBound p * r ^ p.natDegree) ^ next.q := by
    rw [nextProductStage_Q, Polynomial.eval_mul, norm_mul]
    exact mul_le_mul hQ' hfactor (norm_nonneg _)
      (mul_nonneg (polynomialBound_pos _).le (pow_nonneg hrpos.le _))
  let E : ℝ := Real.log (polynomialBound prev.Q) + (prev.Q.natDegree : ℝ) * x +
    (next.q : ℝ) * Real.log (polynomialBound p) +
      (next.q : ℝ) * (p.natDegree : ℝ) * x
  have hUeq : polynomialBound prev.Q * r ^ prev.Q.natDegree *
        (polynomialBound p * r ^ p.natDegree) ^ next.q = Real.exp E := by
    have hBQ : polynomialBound prev.Q = Real.exp (Real.log (polynomialBound prev.Q)) :=
      (Real.exp_log (polynomialBound_pos prev.Q)).symm
    have hBp : polynomialBound p = Real.exp (Real.log (polynomialBound p)) :=
      (Real.exp_log (polynomialBound_pos p)).symm
    have hrE : r = Real.exp x := (Real.exp_log hrpos).symm
    rw [hBQ, hBp, hrE]
    simp only [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    simp only [E]
    ring
  have hlQ : 0 ≤ Real.log (polynomialBound prev.Q) :=
    Real.log_nonneg (one_le_polynomialBound prev.Q)
  have hlp : 0 ≤ Real.log (polynomialBound p) :=
    Real.log_nonneg (one_le_polynomialBound p)
  have hA : 0 ≤ A := (stageA_pos prev.Q).le
  have hD : 0 ≤ (prev.Q.natDegree : ℝ) := by positivity
  have hd : 0 ≤ (p.natDegree : ℝ) := by positivity
  have hx0 : 0 ≤ x := le_trans zero_le_one hx1
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hterm1 : Real.log (polynomialBound prev.Q) ≤
      2 * Real.log (polynomialBound prev.Q) * x ^ 2 := by nlinarith
  have hterm2 : (prev.Q.natDegree : ℝ) * x ≤
      2 * (prev.Q.natDegree : ℝ) * x ^ 2 := by nlinarith
  have hterm3 : (next.q : ℝ) * Real.log (polynomialBound p) ≤
      (2 * A * Real.log (polynomialBound p)) * x ^ 2 := by
    calc
      _ ≤ (2 * A * x) * Real.log (polynomialBound p) :=
        mul_le_mul_of_nonneg_right hqle hlp
      _ ≤ (2 * A * Real.log (polynomialBound p)) * x ^ 2 := by
        have := mul_le_mul_of_nonneg_left hxx (mul_nonneg (by positivity) hlp)
        nlinarith
  have hterm4 : (next.q : ℝ) * (p.natDegree : ℝ) * x ≤
      (2 * A * (p.natDegree : ℝ)) * x ^ 2 := by
    have := mul_le_mul_of_nonneg_right hqle (mul_nonneg hd hx0)
    nlinarith
  have hEle : E ≤ 2 * next.C * x ^ 2 := by
    have hC : next.C = stageGrowthConstant prev.Q p := rfl
    calc
      E ≤ 2 * Real.log (polynomialBound prev.Q) * x ^ 2 +
          2 * (prev.Q.natDegree : ℝ) * x ^ 2 +
          (2 * A * Real.log (polynomialBound p)) * x ^ 2 +
          (2 * A * (p.natDegree : ℝ)) * x ^ 2 :=
        add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4
      _ = 2 * next.C * x ^ 2 := by
        rw [hC]
        simp only [stageGrowthConstant]
        dsimp only [A]
        ring
  exact hraw.trans (by rw [hUeq]; exact Real.exp_le_exp.mpr hEle)

/-! ## The recursive product -/

noncomputable def constructionStages (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    ℕ → ProductStage
  | 0 => initialProductStage
  | n + 1 => nextProductStage φ hφ n (constructionStages φ hφ n)

noncomputable def constructionStage (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) : ProductStage :=
  constructionStages φ hφ (n + 1)

noncomputable def constructionFactor (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) : Polynomial ℂ :=
  let s := constructionStage φ hφ n
  scaledPolynomialFactor (baseLabyrinthPolynomial n) s.T s.q

noncomputable def constructionActivation (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) (n : ℕ) : ℝ :=
  stageActivation (constructionStages φ hφ n).Q n (constructionStage φ hφ n).q

@[simp] lemma constructionStages_zero (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    constructionStages φ hφ 0 = initialProductStage := rfl

@[simp] lemma constructionStages_succ (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    constructionStages φ hφ (n + 1) =
      nextProductStage φ hφ n (constructionStages φ hφ n) := rfl

lemma constructionStage_eq_next (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    constructionStage φ hφ n =
      nextProductStage φ hφ n (constructionStages φ hφ n) := rfl

lemma constructionStage_Q (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    (constructionStage φ hφ n).Q =
      (constructionStages φ hφ n).Q * constructionFactor φ hφ n := by
  rw [constructionStage_eq_next, nextProductStage_Q]
  rfl

lemma constructionStages_Q_eq_prod (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (N : ℕ) :
    (constructionStages φ hφ N).Q =
      ∏ n ∈ Finset.range N, constructionFactor φ hφ n := by
  induction N with
  | zero => simp [initialProductStage]
  | succ N ih =>
      rw [constructionStages_succ, nextProductStage_Q, ih]
      simp only [Finset.prod_range_succ]
      rfl

lemma constructionStage_Q_eq_prod (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    (constructionStage φ hφ n).Q =
      ∏ i ∈ Finset.range (n + 1), constructionFactor φ hφ i := by
  exact constructionStages_Q_eq_prod φ hφ (n + 1)

lemma constructionStage_spec (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    let prev := constructionStages φ hφ n
    let next := constructionStage φ hφ n
    0 < next.q ∧ Real.exp 1 < next.T ∧ 3 * prev.T < next.T ∧
      (∀ r ≥ next.T, next.C + 1 ≤ φ r) ∧
      polynomialBound prev.Q * (3 * next.T) ^ prev.Q.natDegree *
          (1 / 4 : ℝ) ^ next.q ≤ 1 / 4 ∧
      Real.exp ((next.q : ℝ) *
          polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) *
          (3 * prev.T) * next.T⁻¹) - 1 ≤ stageError n := by
  simpa only [constructionStage_eq_next] using
    nextProductStage_spec φ hφ n (constructionStages φ hφ n)

lemma constructionStage_activation_spec (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    Real.exp 1 < constructionActivation φ hφ n ∧
    3 * (constructionStages φ hφ n).T < constructionActivation φ hφ n ∧
    (∀ r ≥ constructionActivation φ hφ n,
      2 * (constructionStage φ hφ n).C + 1 ≤ φ r) ∧
    ((constructionStage φ hφ n).q : ℝ) ≤
      2 * stageA (constructionStages φ hφ n).Q *
        Real.log (constructionActivation φ hφ n) ∧
    Real.exp (((constructionStage φ hφ n).q : ℝ) * polynomialBound
      (polynomialSlope (baseLabyrinthPolynomial n)) * constructionActivation φ hφ n *
        (constructionStage φ hφ n).T⁻¹) - 1 ≤ stageError n := by
  simpa only [constructionStage_eq_next, constructionActivation] using
    nextProductStage_activation_spec φ hφ n (constructionStages φ hφ n)

lemma constructionStage_T_growth (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    3 * (constructionStages φ hφ n).T < (constructionStage φ hφ n).T :=
  (constructionStage_spec φ hφ n).2.2.1

lemma constructionStage_T_gt_exp_one (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    Real.exp 1 < (constructionStage φ hφ n).T :=
  (constructionStage_spec φ hφ n).2.1

lemma constructionStage_factor_close (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 3 * (constructionStages φ hφ n).T) :
    ‖(constructionFactor φ hφ n).eval z - 1‖ ≤ stageError n := by
  simp only [constructionFactor]
  rw [constructionStage_eq_next]
  exact nextProductStage_factor_close φ hφ n (constructionStages φ hφ n) hz

lemma constructionStage_factor_close_activation (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) (n : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ constructionActivation φ hφ n) :
    ‖(constructionFactor φ hφ n).eval z - 1‖ ≤ stageError n := by
  let prev := constructionStages φ hφ n
  let next := constructionStage φ hφ n
  let R := constructionActivation φ hφ n
  have hspec := constructionStage_activation_spec φ hφ n
  have hTpos : 0 < next.T := next.T_pos
  have hRpos : 0 < R := lt_trans (Real.exp_pos 1) hspec.1
  have hRT : R < next.T := by
    unfold R constructionActivation
    rw [constructionStage_eq_next]
    exact stageActivation_lt_scale prev.Q n (nextProductStage φ hφ n prev).q
  have hw : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    rw [← div_eq_inv_mul]
    exact (div_le_one hTpos).2 (hz.trans hRT.le)
  have hbase := polynomial_eval_sub_zero_le (baseLabyrinthPolynomial n) hw
  rw [baseLabyrinthPolynomial_zero] at hbase
  have hpow := norm_pow_sub_one_le_exp
    (a := (baseLabyrinthPolynomial n).eval (((next.T⁻¹ : ℝ) : ℂ) * z)) next.q
  simp only [constructionFactor]
  rw [scaledPolynomialFactor_eval]
  refine hpow.trans (le_trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1) hspec.2.2.2.2)
  have hnormz : ‖(((next.T⁻¹ : ℝ) : ℂ) * z)‖ ≤ R * next.T⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hTpos]
    calc
      next.T⁻¹ * ‖z‖ ≤ next.T⁻¹ * R :=
        mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hTpos.le)
      _ = R * next.T⁻¹ := mul_comm _ _
  have hq0 : 0 ≤ (next.q : ℝ) := by positivity
  change (next.q : ℝ) *
      ‖(baseLabyrinthPolynomial n).eval (((next.T⁻¹ : ℝ) : ℂ) * z) - 1‖ ≤
    (next.q : ℝ) * polynomialBound (polynomialSlope (baseLabyrinthPolynomial n)) *
      R * next.T⁻¹
  calc
    _ ≤ (next.q : ℝ) * (polynomialBound
        (polynomialSlope (baseLabyrinthPolynomial n)) * (R * next.T⁻¹)) :=
      mul_le_mul_of_nonneg_left
        (hbase.trans (mul_le_mul_of_nonneg_left hnormz
          (polynomialBound_pos _).le)) hq0
    _ = _ := by ring

lemma constructionStage_wall (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) {z : ℂ}
    (hz : z ∈ labyrinthSet (n + 2) (constructionStage φ hφ n).T) :
    ‖(constructionStage φ hφ n).Q.eval z‖ ≤ 1 / 4 := by
  rw [constructionStage_eq_next] at hz ⊢
  exact nextProductStage_wall φ hφ n (constructionStages φ hφ n) hz

lemma constructionStage_growth (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) {r : ℝ} (hr : (constructionStage φ hφ n).T ≤ r)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(constructionStage φ hφ n).Q.eval z‖ ≤
      Real.exp ((constructionStage φ hφ n).C * (Real.log r) ^ 2) := by
  rw [constructionStage_eq_next] at hr ⊢
  exact nextProductStage_growth φ hφ n (constructionStages φ hφ n) hr hz

lemma constructionStage_growth_from_activation (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) (n : ℕ) {r : ℝ}
    (hr : constructionActivation φ hφ n ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(constructionStage φ hφ n).Q.eval z‖ ≤
      Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2) := by
  rw [constructionStage_eq_next] at ⊢
  exact nextProductStage_growth_from_activation φ hφ n
    (constructionStages φ hφ n) hr hz

lemma constructionActivation_lt_T (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    constructionActivation φ hφ n < (constructionStage φ hφ n).T := by
  unfold constructionActivation
  rw [constructionStage_eq_next]
  exact stageActivation_lt_scale (constructionStages φ hφ n).Q n
    (nextProductStage φ hφ n (constructionStages φ hφ n)).q

lemma constructionActivation_strictMono (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    StrictMono (constructionActivation φ hφ) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hnext := (constructionStage_activation_spec φ hφ (n + 1)).2.1
  have hltT := constructionActivation_lt_T φ hφ n
  change constructionActivation φ hφ n < constructionActivation φ hφ (n + 1)
  have hTpos := (constructionStage φ hφ n).T_pos
  change 3 * (constructionStage φ hφ n).T < constructionActivation φ hφ (n + 1) at hnext
  nlinarith

lemma constructionFactor_close_of_activation_le (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) {n m : ℕ} (hnm : n ≤ m) {z : ℂ}
    (hz : ‖z‖ ≤ constructionActivation φ hφ n) :
    ‖(constructionFactor φ hφ m).eval z - 1‖ ≤ stageError m := by
  apply constructionStage_factor_close_activation φ hφ m
  exact hz.trans (constructionActivation_strictMono φ hφ |>.monotone hnm)

noncomputable def counterexampleFunction (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    ℂ → ℂ :=
  fun z ↦ @tprod ℂ ℕ NormedField.toNormedCommRing.toCommRing.toCommMonoid
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    (fun n ↦ (constructionFactor φ hφ n).eval z) (SummationFilter.unconditional ℕ)

lemma constructionStages_T_lower (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    (n + 1 : ℝ) ≤ (constructionStages φ hφ n).T := by
  induction n with
  | zero => simp [initialProductStage]
  | succ n ih =>
      have hgrowth := constructionStage_T_growth φ hφ n
      rw [Nat.cast_add, Nat.cast_one]
      change (n : ℝ) + 1 + 1 ≤ (constructionStage φ hφ n).T
      have hn : (0 : ℝ) ≤ n := by positivity
      nlinarith

lemma constructionActivation_tendsto (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (constructionActivation φ hφ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hcast := hN n hn
  have hlarge := (constructionStage_activation_spec φ hφ n).2.1
  have hstage := constructionStages_T_lower φ hφ n
  nlinarith

lemma constructionStages_T_tendsto (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n ↦ (constructionStages φ hφ n).T) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop b))
  exact ⟨N, fun n hn ↦
    (hN n hn).trans (le_trans (by norm_num) (constructionStages_T_lower φ hφ n))⟩

lemma counterexample_hasProdLocallyUniformly (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    HasProdLocallyUniformlyOn
      (fun n z ↦ (constructionFactor φ hφ n).eval z)
      (counterexampleFunction φ hφ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hlarge : ∀ᶠ n : ℕ in atTop,
      R ≤ 3 * (constructionStages φ hφ n).T := by
    have hthree : Tendsto (fun n ↦ 3 * (constructionStages φ hφ n).T)
        atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) (constructionStages_T_tendsto φ hφ)
    exact hthree.eventually (eventually_ge_atTop R)
  have hclose : ∀ᶠ n : ℕ in atTop, ∀ z ∈ K,
      ‖(constructionFactor φ hφ n).eval z - 1‖ ≤ stageError n := by
    filter_upwards [hlarge] with n hn z hz
    exact constructionStage_factor_close φ hφ n ((hR z hz).trans hn)
  have hprod := Summable.hasProdUniformlyOn_nat_one_add hK summable_stageError hclose
    (fun n ↦ (constructionFactor φ hφ n).differentiable.continuous.continuousOn.sub
      continuousOn_const)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hprod ⊢
  unfold counterexampleFunction
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hprod

lemma counterexample_tendstoLocallyUniformly (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    TendstoLocallyUniformlyOn
      (fun N z ↦ ∏ n ∈ Finset.range N, (constructionFactor φ hφ n).eval z)
      (counterexampleFunction φ hφ) atTop Set.univ :=
  (counterexample_hasProdLocallyUniformly φ hφ).tendstoLocallyUniformlyOn_finsetRange

lemma counterexampleFunction_differentiable (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    Differentiable ℂ (counterexampleFunction φ hφ) := by
  rw [← differentiableOn_univ]
  apply (counterexample_tendstoLocallyUniformly φ hφ).differentiableOn
  · filter_upwards [] with N
    have heq :
        (fun z ↦ ∏ n ∈ Finset.range N, (constructionFactor φ hφ n).eval z) =
          fun z ↦ (constructionStages φ hφ N).Q.eval z := by
      funext z
      rw [constructionStages_Q_eq_prod, Polynomial.eval_prod]
    rw [heq]
    exact (constructionStages φ hφ N).Q.differentiableOn
  · exact isOpen_univ

lemma constructionFactor_zero (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) :
    ∃ z : ℂ, (constructionFactor φ hφ n).eval z = 0 := by
  let p := baseLabyrinthPolynomial n
  have hpdeg : 0 < p.degree :=
    Polynomial.natDegree_pos_iff_degree_pos.mp (baseLabyrinthPolynomial_natDegree_pos n)
  obtain ⟨w, hw⟩ := Complex.exists_root hpdeg
  let s := constructionStage φ hφ n
  refine ⟨((s.T : ℝ) : ℂ) * w, ?_⟩
  have hTne : s.T ≠ 0 := s.T_pos.ne'
  have harg : (((s.T⁻¹ : ℝ) : ℂ) * (((s.T : ℝ) : ℂ) * w)) = w := by
    calc
      (((s.T⁻¹ : ℝ) : ℂ) * (((s.T : ℝ) : ℂ) * w)) =
          ((((s.T⁻¹ * s.T : ℝ) : ℂ)) * w) := by push_cast; ring
      _ = w := by rw [inv_mul_cancel₀ hTne]; simp
  simp only [constructionFactor, s, scaledPolynomialFactor_eval]
  rw [harg, hw.eq_zero, zero_pow]
  exact (constructionStage_spec φ hφ n).1.ne'

lemma counterexampleFunction_zero (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    ∃ z : ℂ, counterexampleFunction φ hφ z = 0 := by
  obtain ⟨z, hz⟩ := constructionFactor_zero φ hφ 0
  refine ⟨z, ?_⟩
  unfold counterexampleFunction
  exact tprod_of_exists_eq_zero ⟨0, hz⟩

@[simp] lemma counterexampleFunction_zero_value (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    counterexampleFunction φ hφ 0 = 1 := by
  unfold counterexampleFunction
  have hfactor : ∀ n : ℕ, (constructionFactor φ hφ n).eval 0 = 1 := by
    intro n
    simp [constructionFactor, scaledPolynomialFactor_eval, baseLabyrinthPolynomial_zero]
  simp_rw [hfactor]
  exact tprod_one

lemma counterexampleFunction_nonconstant (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    ∃ z w : ℂ, counterexampleFunction φ hφ z ≠ counterexampleFunction φ hφ w := by
  obtain ⟨z, hz⟩ := counterexampleFunction_zero φ hφ
  refine ⟨z, 0, ?_⟩
  rw [hz, counterexampleFunction_zero_value]
  norm_num

lemma counterexampleFunction_range_unbounded (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    ¬Bornology.IsBounded (Set.range (counterexampleFunction φ hφ)) := by
  intro hbounded
  obtain ⟨z, w, hne⟩ := counterexampleFunction_nonconstant φ hφ
  exact hne ((counterexampleFunction_differentiable φ hφ).apply_eq_apply_of_bounded
    hbounded z w)

lemma tsum_stageError : ∑' n : ℕ, stageError n = 1 / 4 := by
  have heq : stageError = fun n : ℕ ↦ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n := by
    funext n
    rw [stageError, pow_add]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_two]
  norm_num

lemma constructionStages_T_mono (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    Monotone (fun n ↦ (constructionStages φ hφ n).T) := by
  apply monotone_nat_of_le_succ
  intro n
  have hgrowth := constructionStage_T_growth φ hφ n
  have hpos := (constructionStages φ hφ n).T_pos
  change (constructionStages φ hφ n).T ≤ (constructionStage φ hφ n).T
  nlinarith

lemma constructionFactor_close_of_stage_lt (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) {n m : ℕ} (hnm : n + 1 ≤ m)
    {z : ℂ} (hz : ‖z‖ ≤ 3 * (constructionStage φ hφ n).T) :
    ‖(constructionFactor φ hφ m).eval z - 1‖ ≤ stageError m := by
  apply constructionStage_factor_close φ hφ m
  apply hz.trans
  gcongr
  exact constructionStages_T_mono φ hφ hnm

lemma stageError_shift_le (n i : ℕ) : stageError (n + 1 + i) ≤ stageError i := by
  simp only [stageError]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

lemma counterexampleFunction_wall (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    (n : ℕ) {z : ℂ}
    (hz : z ∈ labyrinthSet (n + 2) (constructionStage φ hφ n).T) :
    ‖counterexampleFunction φ hφ z‖ ≤ 1 := by
  have hTpos := (constructionStage φ hφ n).T_pos
  have hznorm := (labyrinthSet_norm_bounds hTpos hz).2
  have hpartial : ∀ N ≥ n + 1,
      ‖∏ i ∈ Finset.range N, (constructionFactor φ hφ i).eval z‖ ≤ 1 := by
    intro N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Finset.prod_range_add, norm_mul]
    have hfirst :
        ‖∏ i ∈ Finset.range (n + 1), (constructionFactor φ hφ i).eval z‖ ≤
          1 / 4 := by
      rw [← Polynomial.eval_prod, ← constructionStage_Q_eq_prod]
      exact constructionStage_wall φ hφ n hz
    let d : ℕ → ℂ := fun i ↦
      (constructionFactor φ hφ (n + 1 + i)).eval z - 1
    have hd (i : ℕ) : ‖d i‖ ≤ stageError (n + 1 + i) := by
      exact constructionFactor_close_of_stage_lt φ hφ
        (n := n) (m := n + 1 + i) (by omega) hznorm.le
    have hsum : ∑ i ∈ Finset.range k, ‖d i‖ ≤ 1 / 4 := by
      calc
        _ ≤ ∑ i ∈ Finset.range k, stageError (n + 1 + i) :=
          Finset.sum_le_sum fun i _ ↦ hd i
        _ ≤ ∑ i ∈ Finset.range k, stageError i :=
          Finset.sum_le_sum fun i _ ↦ stageError_shift_le n i
        _ ≤ ∑' i : ℕ, stageError i :=
          summable_stageError.sum_le_tsum _ fun i _ ↦ (stageError_pos i).le
        _ = 1 / 4 := tsum_stageError
    have htailSub := Finset.norm_prod_one_add_sub_one_le (Finset.range k) d
    have hprodEq :
        (∏ i ∈ Finset.range k,
          (constructionFactor φ hφ (n + 1 + i)).eval z) =
            ∏ i ∈ Finset.range k, (1 + d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have htail :
        ‖∏ i ∈ Finset.range k,
            (constructionFactor φ hφ (n + 1 + i)).eval z‖ ≤ Real.exp (1 / 4) := by
      have hnorm :
          ‖∏ i ∈ Finset.range k, (1 + d i)‖ ≤
            ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + 1 := by
        calc
          _ = ‖((∏ i ∈ Finset.range k, (1 + d i)) - 1) + 1‖ := by ring_nf
          _ ≤ ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = _ := by simp
      have hexp := Real.exp_le_exp.mpr hsum
      calc
        _ = ‖∏ i ∈ Finset.range k, (1 + d i)‖ := congrArg norm hprodEq
        _ ≤ ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + 1 := hnorm
        _ ≤ (Real.exp (∑ i ∈ Finset.range k, ‖d i‖) - 1) + 1 := by
          linarith
        _ = Real.exp (∑ i ∈ Finset.range k, ‖d i‖) := by ring
        _ ≤ Real.exp (1 / 4) := hexp
    have hexp4 : Real.exp (1 / 4 : ℝ) < 4 := by
      exact (Real.exp_lt_exp.mpr (by norm_num : (1 / 4 : ℝ) < 1)).trans
        (Real.exp_one_lt_three.trans (by norm_num))
    nlinarith [mul_le_mul hfirst htail (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / 4)]
  have hpoint := (counterexample_tendstoLocallyUniformly φ hφ).tendsto_at (Set.mem_univ z)
  have hnormlim : Tendsto
      (fun N ↦ ‖∏ i ∈ Finset.range N, (constructionFactor φ hφ i).eval z‖)
      atTop (𝓝 ‖counterexampleFunction φ hφ z‖) :=
    (continuous_norm.tendsto _).comp hpoint
  apply le_of_tendsto hnormlim
  exact eventually_atTop.2 ⟨n + 1, hpartial⟩

lemma exists_activation_interval (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop)
    {r : ℝ} (hr : constructionActivation φ hφ 0 ≤ r) :
    ∃ n : ℕ, constructionActivation φ hφ n ≤ r ∧
      r < constructionActivation φ hφ (n + 1) := by
  have hex : ∃ N : ℕ, r < constructionActivation φ hφ N :=
    (constructionActivation_tendsto φ hφ).eventually (eventually_gt_atTop r) |>.exists
  let N := Nat.find hex
  have hN : r < constructionActivation φ hφ N := Nat.find_spec hex
  have hN0 : N ≠ 0 := by
    intro hzero
    have : r < constructionActivation φ hφ 0 := by simpa [hzero] using hN
    exact (not_lt_of_ge hr) this
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  refine ⟨n, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by omega))
  · simpa [hn] using hN

lemma counterexampleFunction_pointwise_growth (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) {r : ℝ}
    (hr : constructionActivation φ hφ 0 ≤ r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖counterexampleFunction φ hφ z‖ ≤
      Real.exp (φ r * (Real.log r) ^ 2) := by
  obtain ⟨n, hnR, hrnext⟩ := exists_activation_interval φ hφ hr
  have hR1 := (constructionStage_activation_spec φ hφ n).1
  have hr1 : 1 < r :=
    (lt_trans (by norm_num) Real.exp_one_gt_two).trans (hR1.trans_le hnR)
  have hx1 : 1 ≤ Real.log r := by
    rw [← Real.log_exp 1]
    exact (Real.strictMonoOn_log (Real.exp_pos 1) (lt_trans zero_lt_one hr1)
      ((constructionStage_activation_spec φ hφ n).1.trans_le hnR)).le
  have hQ := constructionStage_growth_from_activation φ hφ n hnR hz
  have hphi := (constructionStage_activation_spec φ hφ n).2.2.1 r hnR
  have hpartial : ∀ N ≥ n + 1,
      ‖∏ i ∈ Finset.range N, (constructionFactor φ hφ i).eval z‖ ≤
        Real.exp (φ r * (Real.log r) ^ 2) := by
    intro N hN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
    rw [Finset.prod_range_add, norm_mul]
    have hfirst :
        ‖∏ i ∈ Finset.range (n + 1), (constructionFactor φ hφ i).eval z‖ ≤
          Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2) := by
      rw [← Polynomial.eval_prod, ← constructionStage_Q_eq_prod]
      exact hQ
    let d : ℕ → ℂ := fun i ↦
      (constructionFactor φ hφ (n + 1 + i)).eval z - 1
    have hd (i : ℕ) : ‖d i‖ ≤ stageError (n + 1 + i) := by
      apply constructionFactor_close_of_activation_le φ hφ
        (n := n + 1) (m := n + 1 + i) (by omega)
      exact hz.trans hrnext.le
    have hsum : ∑ i ∈ Finset.range k, ‖d i‖ ≤ 1 / 4 := by
      calc
        _ ≤ ∑ i ∈ Finset.range k, stageError (n + 1 + i) :=
          Finset.sum_le_sum fun i _ ↦ hd i
        _ ≤ ∑ i ∈ Finset.range k, stageError i :=
          Finset.sum_le_sum fun i _ ↦ stageError_shift_le n i
        _ ≤ ∑' i : ℕ, stageError i :=
          summable_stageError.sum_le_tsum _ fun i _ ↦ (stageError_pos i).le
        _ = 1 / 4 := tsum_stageError
    have htailSub := Finset.norm_prod_one_add_sub_one_le (Finset.range k) d
    have hprodEq :
        (∏ i ∈ Finset.range k,
          (constructionFactor φ hφ (n + 1 + i)).eval z) =
            ∏ i ∈ Finset.range k, (1 + d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [d, sub_eq_add_neg, add_left_comm, add_comm]
    have htail :
        ‖∏ i ∈ Finset.range k,
            (constructionFactor φ hφ (n + 1 + i)).eval z‖ ≤ Real.exp (1 / 4) := by
      have hnorm :
          ‖∏ i ∈ Finset.range k, (1 + d i)‖ ≤
            ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + 1 := by
        calc
          _ = ‖((∏ i ∈ Finset.range k, (1 + d i)) - 1) + 1‖ := by ring_nf
          _ ≤ ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
          _ = _ := by simp
      calc
        _ = ‖∏ i ∈ Finset.range k, (1 + d i)‖ := congrArg norm hprodEq
        _ ≤ ‖(∏ i ∈ Finset.range k, (1 + d i)) - 1‖ + 1 := hnorm
        _ ≤ (Real.exp (∑ i ∈ Finset.range k, ‖d i‖) - 1) + 1 := by
          linarith
        _ = Real.exp (∑ i ∈ Finset.range k, ‖d i‖) := by ring
        _ ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr hsum
    have hproduct :
        Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2) *
            Real.exp (1 / 4) =
          Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2 + 1 / 4) := by
      rw [← Real.exp_add]
    have hexponents :
        2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2 + 1 / 4 ≤
          φ r * (Real.log r) ^ 2 := by
      have hx2 : 1 ≤ (Real.log r) ^ 2 := by nlinarith
      nlinarith
    calc
      _ ≤ Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2) *
          Real.exp (1 / 4) :=
        mul_le_mul hfirst htail (norm_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (constructionStage φ hφ n).C * (Real.log r) ^ 2 + 1 / 4) :=
        hproduct
      _ ≤ _ := Real.exp_le_exp.mpr hexponents
  have hpoint := (counterexample_tendstoLocallyUniformly φ hφ).tendsto_at (Set.mem_univ z)
  have hnormlim : Tendsto
      (fun N ↦ ‖∏ i ∈ Finset.range N, (constructionFactor φ hφ i).eval z‖)
      atTop (𝓝 ‖counterexampleFunction φ hφ z‖) :=
    (continuous_norm.tendsto _).comp hpoint
  apply le_of_tendsto hnormlim
  exact eventually_atTop.2 ⟨n + 1, hpartial⟩

lemma maximumModulus_le_of_forall_sphere {f : ℂ → ℂ} {r B : ℝ}
    (hr : 0 ≤ r) (hB : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ B) :
    maximumModulus f r ≤ B := by
  let z : {z : ℂ // ‖z‖ = r} := ⟨(r : ℂ), by simp [abs_of_nonneg hr]⟩
  letI : Nonempty {z : ℂ // ‖z‖ = r} := ⟨z⟩
  unfold maximumModulus
  exact ciSup_le fun z ↦ hB z z.property

lemma maximumModulus_nonneg_of_forall_sphere {f : ℂ → ℂ} {r B : ℝ}
    (hr : 0 ≤ r) (hB : ∀ z : ℂ, ‖z‖ = r → ‖f z‖ ≤ B) :
    0 ≤ maximumModulus f r := by
  let z : {z : ℂ // ‖z‖ = r} :=
    ⟨(r : ℂ), by simp [abs_of_nonneg hr]⟩
  have hbdd : BddAbove (Set.range (fun w : {z : ℂ // ‖z‖ = r} ↦ ‖f w‖)) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hB w w.property
  exact (norm_nonneg (f z)).trans (le_ciSup hbdd z)

lemma counterexampleFunction_maximumModulus_growth (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) {r : ℝ}
    (hr : constructionActivation φ hφ 0 ≤ r) :
    Real.log (maximumModulus (counterexampleFunction φ hφ) r) ≤
      φ r * (Real.log r) ^ 2 := by
  have hR1 := (constructionStage_activation_spec φ hφ 0).1
  have hr0 : 0 ≤ r := le_trans (Real.exp_pos 1).le (hR1.le.trans hr)
  have hsphere : ∀ z : ℂ, ‖z‖ = r →
      ‖counterexampleFunction φ hφ z‖ ≤ Real.exp (φ r * (Real.log r) ^ 2) := by
    intro z hz
    exact counterexampleFunction_pointwise_growth φ hφ hr hz.le
  have hM := maximumModulus_le_of_forall_sphere hr0 hsphere
  have hM0 := maximumModulus_nonneg_of_forall_sphere hr0 hsphere
  have hphi : 0 ≤ φ r := by
    have hs := (constructionStage_activation_spec φ hφ 0).2.2.1 r hr
    have hC := stageGrowthConstant_nonneg
      (constructionStages φ hφ 0).Q (baseLabyrinthPolynomial 0)
    change 2 * (constructionStage φ hφ 0).C + 1 ≤ φ r at hs
    have hC' : 0 ≤ (constructionStage φ hφ 0).C := by
      rw [constructionStage_eq_next]
      exact hC
    linarith
  by_cases hzero : maximumModulus (counterexampleFunction φ hφ) r = 0
  · rw [hzero, Real.log_zero]
    exact mul_nonneg hphi (sq_nonneg _)
  · exact (Real.log_le_iff_le_exp (lt_of_le_of_ne hM0 (Ne.symm hzero))).2 hM

lemma counterexampleFunction_hasGrowth (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    HasGolbergEremenkoGrowth φ (counterexampleFunction φ hφ) := by
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [eventually_ge_atTop (constructionActivation φ hφ 0)] with r hr
  simpa using counterexampleFunction_maximumModulus_growth φ hφ hr

noncomputable def slowGrowth (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun r ↦ min (φ r) r

lemma slowGrowth_tendsto {φ : ℝ → ℝ} (hφ : Tendsto φ atTop atTop) :
    Tendsto (slowGrowth φ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1
    (hφ.eventually (eventually_ge_atTop b))
  refine ⟨max R₁ b, fun r hr ↦ ?_⟩
  exact le_min (hR₁ r (le_trans (le_max_left _ _) hr))
    (le_trans (le_max_right _ _) hr)

lemma slowGrowth_le_left (φ : ℝ → ℝ) (r : ℝ) : slowGrowth φ r ≤ φ r := min_le_left _ _

lemma slowGrowth_le_right (φ : ℝ → ℝ) (r : ℝ) : slowGrowth φ r ≤ r := min_le_right _ _

lemma counterexampleFunction_hasGrowth_of_slowGrowth (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    HasGolbergEremenkoGrowth φ
      (counterexampleFunction (slowGrowth φ) (slowGrowth_tendsto hφ)) := by
  let ψ := slowGrowth φ
  let hψ := slowGrowth_tendsto hφ
  refine ⟨1, zero_le_one, ?_⟩
  filter_upwards [eventually_ge_atTop (constructionActivation ψ hψ 0)] with r hr
  have hg := counterexampleFunction_maximumModulus_growth ψ hψ hr
  have hle : ψ r * (Real.log r) ^ 2 ≤ φ r * (Real.log r) ^ 2 :=
    mul_le_mul_of_nonneg_right (slowGrowth_le_left φ r) (sq_nonneg _)
  simpa only [one_mul] using hg.trans hle

lemma counterexampleFunction_finiteOrder_of_slowGrowth (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    EntireOfFiniteOrder
      (counterexampleFunction (slowGrowth φ) (slowGrowth_tendsto hφ)) := by
  let ψ := slowGrowth φ
  let hψ := slowGrowth_tendsto hφ
  let a := constructionActivation ψ hψ 0
  let f := counterexampleFunction ψ hψ
  refine ⟨counterexampleFunction_differentiable ψ hψ,
    Real.exp (a ^ 3), (Real.exp_pos _).le, 3, by norm_num, ?_⟩
  intro z
  let r := max a ‖z‖
  have har : a ≤ r := le_max_left _ _
  have hzr : ‖z‖ ≤ r := le_max_right _ _
  have ha1 : 1 < a :=
    (lt_trans (by norm_num) Real.exp_one_gt_two).trans
      (constructionStage_activation_spec ψ hψ 0).1
  have hr1 : 1 < r := ha1.trans_le har
  have hr0 : 0 ≤ r := (lt_trans zero_lt_one hr1).le
  have ha0 : 0 ≤ a := (lt_trans zero_lt_one ha1).le
  have hg : ‖f z‖ ≤ Real.exp (ψ r * (Real.log r) ^ 2) :=
    counterexampleFunction_pointwise_growth ψ hψ har hzr
  have hψ0 : 0 ≤ ψ r := by
    have hs := (constructionStage_activation_spec ψ hψ 0).2.2.1 r har
    have hC : 0 ≤ (constructionStage ψ hψ 0).C := by
      rw [constructionStage_eq_next]
      exact stageGrowthConstant_nonneg _ _
    linarith
  have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hr1.le
  have hlogle : Real.log r ≤ r := Real.log_le_self hr0
  have hsquare : (Real.log r) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ hlog0 hlogle 2
  have hexponent : ψ r * (Real.log r) ^ 2 ≤ r ^ 3 := by
    calc
      _ ≤ r * r ^ 2 := mul_le_mul (slowGrowth_le_right φ r) hsquare
        (sq_nonneg _) hr0
      _ = r ^ 3 := by ring
  have hrpow : r ^ 3 ≤ a ^ 3 + ‖z‖ ^ 3 := by
    dsimp only [r]
    rw [max_def]
    split_ifs with h
    · exact le_add_of_nonneg_left (pow_nonneg ha0 3)
    · exact le_add_of_nonneg_right (pow_nonneg (norm_nonneg z) 3)
  calc
    ‖f z‖ ≤ Real.exp (ψ r * (Real.log r) ^ 2) := hg
    _ ≤ Real.exp (r ^ 3) := Real.exp_le_exp.mpr hexponent
    _ ≤ Real.exp (a ^ 3 + ‖z‖ ^ 3) := Real.exp_le_exp.mpr hrpow
    _ = Real.exp (a ^ 3) * Real.exp (‖z‖ ^ (3 : ℝ)) := by
      rw [Real.exp_add]
      norm_num

lemma constructionStage_T_tendsto (φ : ℝ → ℝ) (hφ : Tendsto φ atTop atTop) :
    Tendsto (fun n ↦ (constructionStage φ hφ n).T) atTop atTop := by
  exact (constructionStages_T_tendsto φ hφ).comp (tendsto_add_atTop_nat 1)

lemma counterexampleFunction_hasEscapingBarriers (φ : ℝ → ℝ)
    (hφ : Tendsto φ atTop atTop) :
    HasEscapingBarriers (counterexampleFunction φ hφ) := by
  let T : ℕ → ℝ := fun n ↦ (constructionStage φ hφ n).T
  refine ⟨(fun n ↦ labyrinthSet (n + 2) (T n)),
    (fun n ↦ 2 * T n), (fun n ↦ 3 * T n),
    (fun n ↦ 2 * (n + 2 - 1 : ℕ) * T n), ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact mul_pos (by norm_num) (constructionStage φ hφ n).T_pos
  · exact Filter.Tendsto.const_mul_atTop (by norm_num) (constructionStage_T_tendsto φ hφ)
  · exact Filter.Tendsto.const_mul_atTop (by norm_num) (constructionStage_T_tendsto φ hφ)
  · have hnat : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop :=
      by simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hlim := Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2 / 3) hnat
    apply hlim.congr'
    filter_upwards with n
    have hTne : T n ≠ 0 := (constructionStage φ hφ n).T_pos.ne'
    change (constructionStage φ hφ n).T ≠ 0 at hTne
    simp only [T]
    rw [show n + 2 - 1 = n + 1 by omega]
    push_cast
    field_simp
  · intro n
    constructor
    · intro z hz
      exact counterexampleFunction_wall φ hφ n hz
    · exact labyrinth_isLengthBarrier (n + 2) (constructionStage φ hφ n).T_pos

lemma lengthInDisc_nonneg (γ : ℝ → ℂ) (r : ℝ) :
    0 ≤ lengthInDisc γ r := ENNReal.toReal_nonneg

/-- The purely geometric last step of the counterexample: increasingly expensive bounded-value
walls rule out every linear-length asymptotic curve. -/
theorem not_hasLinearLength_of_hasEscapingBarriers {f : ℂ → ℂ}
    (hf : HasEscapingBarriers f) {γ : ℝ → ℂ} (hγ : IsAsymptoticPath f γ) :
    ¬HasLinearLength γ := by
  rintro hlinear
  unfold HasLinearLength at hlinear
  rw [Asymptotics.isBigO_iff] at hlinear
  obtain ⟨c, hc⟩ := hlinear
  obtain ⟨S, inner, outer, cost, houterpos, hinner, houter, hratio, hwall⟩ := hf
  obtain ⟨t₀, ht₀⟩ :=
    eventually_atTop.1 (hγ.2.2.eventually (eventually_gt_atTop 1))
  replace ht₀ : ∀ t ≥ max t₀ 0, 1 < ‖f (γ t)‖ := fun t ht ↦ ht₀ t (le_trans (le_max_left _ _) ht)
  let t₀' : ℝ := max t₀ 0
  have hO : ∀ᶠ n : ℕ in atTop,
      ‖lengthInDisc γ (outer n)‖ ≤ c * ‖outer n‖ := houter.eventually hc
  have hinside : ∀ᶠ n : ℕ in atTop, ‖γ t₀'‖ < inner n :=
    hinner.eventually (eventually_gt_atTop ‖γ t₀'‖)
  have hlarge : ∀ᶠ n : ℕ in atTop, c < cost n / outer n :=
    hratio.eventually (eventually_gt_atTop c)
  obtain ⟨n, hnO, hninside, hnlarge⟩ := (hO.and (hinside.and hlarge)).exists
  have hcost : cost n ≤ lengthInDisc γ (outer n) :=
    hwall n |>.2 γ hγ.1 hγ.2.1 t₀' (le_max_right _ _) hninside (by
      intro t ht hmem
      exact (not_lt_of_ge (hwall n |>.1 _ hmem)) (ht₀ t ht))
  rw [Real.norm_of_nonneg (lengthInDisc_nonneg γ (outer n)),
    Real.norm_of_nonneg (houterpos n).le] at hnO
  have hstrict : c * outer n < cost n :=
    (lt_div_iff₀ (houterpos n)).mp hnlarge
  linarith

/-- Gol'dberg and Eremenko's negative resolution of Erdős Problem 1115.  For every prescribed
divergent loss `φ` above Hayman's `(log r)²` threshold there is a genuinely nonconstant
finite-order entire function with that growth, but no arclength-parametrized asymptotic curve over
infinity has length `O(r)` in the disk of radius `r`.  The escaping barriers are retained in the
conclusion as the explicit, non-vacuous geometric certificate behind the last assertion. -/
theorem not_erdos_1115 :
    ∀ φ : ℝ → ℝ, Tendsto φ atTop atTop →
      ∃ f : ℂ → ℂ,
        (∃ z w : ℂ, f z ≠ f w) ∧
        ¬Bornology.IsBounded (Set.range f) ∧
        EntireOfFiniteOrder f ∧
        HasGolbergEremenkoGrowth φ f ∧
        HasEscapingBarriers f ∧
        ∀ γ : ℝ → ℂ, IsAsymptoticPath f γ → ¬HasLinearLength γ := by
  intro φ hφ
  let ψ := slowGrowth φ
  let hψ : Tendsto ψ atTop atTop := slowGrowth_tendsto hφ
  let f := counterexampleFunction ψ hψ
  have hbarriers : HasEscapingBarriers f :=
    counterexampleFunction_hasEscapingBarriers ψ hψ
  refine ⟨f, counterexampleFunction_nonconstant ψ hψ,
    counterexampleFunction_range_unbounded ψ hψ,
    counterexampleFunction_finiteOrder_of_slowGrowth φ hφ,
    counterexampleFunction_hasGrowth_of_slowGrowth φ hφ,
    hbarriers, ?_⟩
  intro γ hγ
  exact not_hasLinearLength_of_hasEscapingBarriers hbarriers hγ

#print axioms not_erdos_1115

end Erdos1115

alias _root_.Erdos1115.erdos_1115 := _root_.Erdos1115.not_erdos_1115
