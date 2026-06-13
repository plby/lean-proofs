/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1044.
https://www.erdosproblems.com/forum/thread/1044

Informal authors:
- Quanyu Tang

Formal authors:
- Aristotle
- Lorenzo Luccioli

URLs:
- https://www.erdosproblems.com/forum/thread/1044#post-6012
- https://github.com/QuanyuTang/erdos-problem-1044/blob/main/On_Erd%C5%91s_Problem_1044.pdf
- https://gist.githubusercontent.com/LorenzoLuccioli/c3ace69881872112109a6c31b7a87cfc/raw
-/
/-
  Formalization of Erdős Problem #1044 in a single file.

  This file is the packaged proof development for the main result

    `Erdos1044.erdos_problem_1044 : lambdaInf = 2`.

  It imports only `Mathlib` and contains all definitions, lemmas, and proofs
  needed on the live dependency path to the main theorem. Fixed-degree side
  results from the earlier split development have been removed from this file.
-/
import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

/-! ### From Defs.lean -/

/-
  Formalization of Erdős Problem #1044
  "On Erdős Problem #1044" by Quanyu Tang

  This file contains the core definitions.
-/

open Polynomial MeasureTheory Topology Set Metric

noncomputable section

namespace Erdos1044

/-! ## Core Definitions -/

/-- The Beta function B(x,y) = Γ(x)Γ(y)/Γ(x+y) -/
def betaFn (x y : ℝ) : ℝ := Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)

/-- The lemniscate region Ω(f) = {z ∈ ℂ : |f(z)| < 1} -/
def OmegaSet (f : Polynomial ℂ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < 1}

/-
Ω(f) is open since |f| is continuous.
-/
lemma omegaSet_isOpen (f : Polynomial ℂ) : IsOpen (OmegaSet f) := by
  exact isOpen_lt ( f.continuous.norm ) continuous_const

/-- The boundary length of the connected component of Ω(f) containing a point z,
    measured by 1-dimensional Hausdorff measure. -/
def componentBoundaryLength (f : Polynomial ℂ) (z : ℂ) : ENNReal :=
  μH[(1 : ℝ)] (frontier (connectedComponentIn (OmegaSet f) z))

/-- Λ(f) = supremum of boundary lengths of connected components of Ω(f) -/
def LambdaFn (f : Polynomial ℂ) : ENNReal :=
  ⨆ z ∈ OmegaSet f, componentBoundaryLength f z

/-- A monic polynomial with all roots in the closed unit disk -/
def IsAdmissible (f : Polynomial ℂ) : Prop :=
  f.Monic ∧ ∀ z : ℂ, f.IsRoot z → ‖z‖ ≤ 1

/-- λ = inf_f Λ(f) over all admissible polynomials of any degree ≥ 1 -/
def lambdaInf : ENNReal :=
  ⨅ (f : Polynomial ℂ) (_ : IsAdmissible f ∧ f.natDegree ≥ 1), LambdaFn f

/-- The model polynomial f_n(z) = z^n - 1 -/
def modelPoly (n : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ n - Polynomial.C 1

/-- The lemniscate constant L_n = (2^(1/n)/n) · B(1/2, 1/(2n)),
    which equals the boundary length of each component of Ω(z^n - 1). -/
def lemniscateLength (n : ℕ) : ℝ :=
  (2 : ℝ) ^ ((1 : ℝ) / n) / n * betaFn (1/2) (1/(2 * ↑n))

/-- The parametric curve for one petal of the lemniscate |z^n - 1| = 1,
    the petal containing z = 2^{1/n} (the point on the positive real axis).
    γ(θ) = (2cos(nθ))^{1/n} · e^{iθ} for θ ∈ [-π/(2n), π/(2n)].

    We use `max 0 (...)` so the definition is globally well-defined;
    for θ in the valid range, cos(nθ) > 0 so the max is redundant. -/
def lemniscatePetalCurve (n : ℕ) (θ : ℝ) : ℂ :=
  ((max 0 (2 * Real.cos (↑n * θ))) ^ ((1 : ℝ) / ↑n) : ℝ) *
    Complex.exp (↑θ * Complex.I)

end Erdos1044


/-! ### From CurveDiameter.lean -/

/-
  Lemma 3.1: For a closed rectifiable curve, length ≥ 2 · diameter.
  Lemma 4.2: For a bounded open set, diam(closure U) = diam(frontier U).
-/

open Set Metric MeasureTheory Topology

noncomputable section

namespace Erdos1044

/-! ## Lemma 3.1: Closed curve length ≥ 2 · diameter -/

/-
**Lemma 3.1**. For a closed rectifiable curve γ : [a, b] → E with γ(a) = γ(b),
    the total variation is at least twice the diameter of the image.
-/
theorem closed_curve_length_ge_two_diam {E : Type*} [PseudoEMetricSpace E]
    {a b : ℝ} (_hab : a ≤ b) (γ : ℝ → E) (hclosed : γ a = γ b) :
    2 * Metric.ediam (γ '' Icc a b) ≤ eVariationOn γ (Icc a b) := by
      -- By definition of $ediam$, we know that for any $x, y \in \gamma(Icc a b)$, $edist(x, y) \leq ediam(\gamma(Icc a b))$.
      suffices h_edist_le_ediam : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, edist (γ x) (γ y) ≤ eVariationOn γ (Set.Icc a b) / 2 by
        convert mul_le_mul_right ( Metric.ediam_le fun x hx y hy => ?_ ) ( 2 : ENNReal ) using 1;
        rw [ ENNReal.mul_div_cancel' ] <;> norm_num;
        aesop;
      intro x hx y hy
      by_cases hxy : x ≤ y;
      · -- By the properties of the variation, we have:
        have h_var : eVariationOn γ (Set.Icc a b) ≥ eVariationOn γ (Set.Icc a x) + eVariationOn γ (Set.Icc x y) + eVariationOn γ (Set.Icc y b) := by
          rw [ ← eVariationOn.union, ← eVariationOn.union ];
          refine eVariationOn.mono _ ?_;
          grind +splitImp;
          exacts [ y, ⟨ Or.inr ⟨ by linarith [ hx.1, hx.2, hy.1, hy.2 ], by linarith [ hx.1, hx.2, hy.1, hy.2 ] ⟩, fun z hz => by cases hz <;> linarith [ Set.mem_Icc.mp ‹_› ] ⟩, ⟨ by constructor <;> linarith [ hx.1, hx.2, hy.1, hy.2 ], fun z hz => by linarith [ Set.mem_Icc.mp hz ] ⟩, x, ⟨ by constructor <;> linarith [ hx.1, hx.2, hy.1, hy.2 ], fun z hz => by linarith [ Set.mem_Icc.mp hz ] ⟩, ⟨ by constructor <;> linarith [ hx.1, hx.2, hy.1, hy.2 ], fun z hz => by linarith [ Set.mem_Icc.mp hz ] ⟩ ];
        -- By the properties of the variation, we have $eVariationOn γ (Icc a x) ≥ edist (γ a) (γ x)$ and $eVariationOn γ (Icc y b) ≥ edist (γ y) (γ b)$.
        have h_var_ax : eVariationOn γ (Set.Icc a x) ≥ edist (γ a) (γ x) := by
          apply_rules [ eVariationOn.edist_le ];
          · aesop;
          · aesop
        have h_var_yb : eVariationOn γ (Set.Icc y b) ≥ edist (γ y) (γ b) := by
          convert eVariationOn.edist_le _ _ _ using 1;
          · aesop;
          · aesop;
        -- By the properties of the variation, we have $eVariationOn γ (Icc x y) ≥ edist (γ x) (γ y)$.
        have h_var_xy : eVariationOn γ (Set.Icc x y) ≥ edist (γ x) (γ y) := by
          apply_rules [ eVariationOn.edist_le ];
          · aesop;
          · aesop;
        rw [ ENNReal.le_div_iff_mul_le ] <;> norm_num;
        refine le_trans ?_ h_var;
        rw [ mul_two ];
        rw [ add_right_comm ];
        refine le_trans ?_ ( add_le_add ( add_le_add h_var_ax h_var_yb ) h_var_xy );
        gcongr;
        rw [ ← hclosed ];
        simpa only [ edist_comm ] using edist_triangle ( γ x ) ( γ a ) ( γ y );
      · have h_sum_ge : eVariationOn γ (Set.Icc a y) + eVariationOn γ (Set.Icc y x) + eVariationOn γ (Set.Icc x b) ≤ eVariationOn γ (Set.Icc a b) := by
          have h_sum_ge : eVariationOn γ (Set.Icc a y ∪ Set.Icc y x ∪ Set.Icc x b) ≤ eVariationOn γ (Set.Icc a b) := by
            apply_rules [ eVariationOn.mono ];
            exact Set.union_subset ( Set.union_subset ( Set.Icc_subset_Icc le_rfl hy.2 ) ( Set.Icc_subset_Icc hy.1 hx.2 ) ) ( Set.Icc_subset_Icc hx.1 le_rfl );
          refine le_trans ?_ h_sum_ge;
          rw [ eVariationOn.union, eVariationOn.union ] <;> norm_num [ Set.Icc_subset_Icc, hx.1, hx.2, hy.1, hy.2, le_of_not_ge hxy ];
          exacts [ y, ⟨ ⟨ by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩, fun z hz => by linarith [ hz.2 ] ⟩, ⟨ ⟨ by linarith [ hy.1 ], by linarith [ hy.2 ] ⟩, fun z hz => by linarith [ hz.1 ] ⟩, x, ⟨ ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩, fun z hz => by linarith [ hz.2 ] ⟩, ⟨ ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ] ⟩, fun z hz => by linarith [ hz.1 ] ⟩ ];
        have h_sum_ge : eVariationOn γ (Set.Icc a y) ≥ edist (γ a) (γ y) ∧ eVariationOn γ (Set.Icc y x) ≥ edist (γ y) (γ x) ∧ eVariationOn γ (Set.Icc x b) ≥ edist (γ x) (γ b) := by
          exact ⟨ by simpa using eVariationOn.edist_le γ ( Set.left_mem_Icc.mpr hy.1 ) ( Set.right_mem_Icc.mpr hy.1 ), by simpa using eVariationOn.edist_le γ ( Set.left_mem_Icc.mpr ( by linarith [ hy.1, hy.2 ] ) ) ( Set.right_mem_Icc.mpr ( by linarith [ hy.1, hy.2 ] ) ), by simpa using eVariationOn.edist_le γ ( Set.left_mem_Icc.mpr ( by linarith [ hx.1, hx.2 ] ) ) ( Set.right_mem_Icc.mpr ( by linarith [ hx.1, hx.2 ] ) ) ⟩;
        have h_sum_ge : edist (γ a) (γ y) + edist (γ x) (γ b) ≥ edist (γ y) (γ x) := by
          rw [ hclosed ];
          rw [ edist_comm ( γ x ) ( γ b ) ] ; exact edist_triangle_left _ _ _;
        rw [ ENNReal.le_div_iff_mul_le ] <;> norm_num;
        rw [ mul_two, edist_comm ];
        refine le_trans ?_ ‹_›;
        refine le_trans ?_ ( add_le_add_three ( show eVariationOn γ ( Icc a y ) ≥ edist ( γ a ) ( γ y ) from ?_ ) ( show eVariationOn γ ( Icc y x ) ≥ edist ( γ y ) ( γ x ) from ?_ ) ( show eVariationOn γ ( Icc x b ) ≥ edist ( γ x ) ( γ b ) from ?_ ) );
        · rw [ add_right_comm ] ; gcongr;
        · grobner;
        · lia;
        · aesop

/-! ## Lemma 4.2: Diameter of bounded open set equals diameter of boundary -/

/-
Helper: In a normed space, the diameter-achieving points of a compact set
    that equals the closure of an open set must lie on the frontier.
    If a ∈ interior U and (a, b) maximizes dist over closure U, then we can
    perturb a in the direction away from b while staying in U, increasing the distance.
-/
lemma dist_lt_diam_of_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {U : Set E}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {a b : E} (ha : a ∈ U) (hb : b ∈ closure U) (hab : a ≠ b) :
    dist a b < Metric.diam (closure U) := by
      -- Since $a$ is in the interior of $U$, we can find a point $a'$ in $U$ such that $\|a' - b\| > \|a - b\|$.
      obtain ⟨a', ha', h_dist⟩ : ∃ a' ∈ U, dist a' b > dist a b := by
        -- Since $a$ is in the interior of $U$, we can find a point $a'$ in $U$ such that $\|a' - b\| > \|a - b\|$ by moving $a$ away from $b$.
        obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball a ε ⊆ U := by
          exact Metric.isOpen_iff.1 hU_open a ha;
        -- Let $v = a - b$, so $v \neq 0$. Let $\delta = \min(\epsilon / 2, 1)$. Define $a' = a + \delta \cdot \frac{v}{\|v\|}$.
        set v : E := a - b
        have hv_ne_zero : v ≠ 0 := by
          exact sub_ne_zero_of_ne hab
        set δ := min (ε / 2) 1 with hδ_def
        use a + δ • (‖v‖⁻¹ • v);
        refine ⟨ hε ?_, ?_ ⟩;
        · simp +decide [ norm_smul, hv_ne_zero ];
          rw [ abs_of_nonneg ] <;> cases min_cases ( ε / 2 ) 1 <;> linarith;
        · rw [ dist_eq_norm, dist_eq_norm ];
          rw [ show a + δ • ‖v‖⁻¹ • v - b = ( 1 + δ * ‖v‖⁻¹ ) • ( a - b ) by
                simp +decide [ add_smul, smul_smul ];
                abel1, norm_smul, Real.norm_of_nonneg ( by positivity ) ];
          exact lt_mul_of_one_lt_left ( norm_pos_iff.mpr hv_ne_zero ) ( lt_add_of_pos_right _ ( mul_pos ( lt_min ( half_pos hε_pos ) zero_lt_one ) ( inv_pos.mpr ( norm_pos_iff.mpr hv_ne_zero ) ) ) );
      refine lt_of_lt_of_le h_dist ( ?_ : dist a' b ≤ diam ( closure U ) );
      refine le_trans
        (dist_le_diam_of_mem (s := closure U) hU_bdd.closure (subset_closure ha') hb) ?_;
      exact le_rfl

/-
**Lemma 4.2**. If U is a bounded open set in a proper normed space, then
    diam(closure U) = diam(frontier U).

    Proof: frontier U ⊆ closure U gives ≤. For ≥, since closure U is compact
    (proper space + bounded), the diameter is achieved at some a, b ∈ closure U.
    By dist_lt_diam_of_interior, neither a nor b can be in U (interior), so both
    are in frontier U. Thus diam(closure U) = dist a b ≤ diam(frontier U).
-/
theorem diam_closure_eq_diam_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {U : Set E}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) (hU_ne : U.Nonempty) :
    Metric.diam (closure U) = Metric.diam (frontier U) := by
      -- Since the closure of U is compact and the distance function is continuous, there exist points a and b in the closure of U such that the distance between them is equal to the diameter of the closure of U.
      obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : E, a ∈ closure U ∧ b ∈ closure U ∧ dist a b = Metric.diam (closure U) := by
        have h_compact : IsCompact (closure U ×ˢ closure U) := by
          exact IsCompact.prod ( hU_bdd.isCompact_closure ) ( hU_bdd.isCompact_closure );
        have h_continuous : ContinuousOn (fun p : E × E => dist p.1 p.2) (closure U ×ˢ closure U) := by
          fun_prop;
        obtain ⟨ p, hp ⟩ := h_compact.exists_isMaxOn ( Set.Nonempty.prod hU_ne.closure hU_ne.closure ) h_continuous;
        refine ⟨ p.1, p.2, hp.1.1, hp.1.2, le_antisymm ?_ ?_ ⟩;
        · exact Metric.dist_le_diam_of_mem ( hU_bdd.closure ) hp.1.1 hp.1.2;
        · refine Metric.diam_le_of_forall_dist_le ?_ ?_;
          · exact dist_nonneg;
          · exact fun x hx y hy => hp.2 ( Set.mk_mem_prod hx hy );
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U;
      · by_cases hab' : a = b;
        · simp_all +decide [ Metric.diam ];
          rw [ eq_comm, ENNReal.toReal_eq_zero_iff ] at hab;
          cases hab <;> simp_all +decide [ ediam ];
          · rw [ show U = { b } by exact Set.eq_singleton_iff_unique_mem.mpr ⟨ hbU, fun x hx => ‹∀ i ∈ U, ∀ i_2 ∈ U, i = i_2› x hx b hbU ⟩ ] ; simp +decide [ frontier_eq_closure_inter_closure ];
            rw [ eq_comm, ENNReal.toReal_eq_zero_iff ];
            simp +decide [ edist_dist ];
          · -- Since $U$ is bounded, the diameter of $U$ is finite.
            have h_diam_finite : ∃ M : ℝ, ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ M := by
              exact isBounded_iff.mp hU_bdd
            obtain ⟨ M, hM ⟩ := h_diam_finite;
            refine absurd ‹⨆ x ∈ U, ⨆ y ∈ U, edist x y = ⊤› ( ne_of_lt ?_ );
            refine lt_of_le_of_lt (b := ENNReal.ofReal M)
              (iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_) ?_;
            · simpa [edist_dist] using ENNReal.ofReal_le_ofReal (hM x hx y hy);
            · exact ENNReal.ofReal_lt_top;
        · exact absurd hab ( ne_of_lt ( dist_lt_diam_of_interior hU_open hU_bdd haU hb hab' ) );
      · have := dist_lt_diam_of_interior hU_open hU_bdd haU hb ( by aesop );
        linarith;
      · have := dist_lt_diam_of_interior hU_open hU_bdd hbU ha ( by aesop );
        simp_all +decide [ dist_comm ];
      · rw [ ← hab, frontier_eq_closure_inter_closure ];
        refine le_antisymm ?_ ?_;
        · refine le_trans (b := dist a b) ?_ ( Metric.dist_le_diam_of_mem
            (s := closure U ∩ closure Uᶜ)
            (hU_bdd.closure.subset Set.inter_subset_left) ?_ ?_ );
          exact le_rfl;
          · exact ⟨ ha, subset_closure ( by aesop ) ⟩;
          · exact ⟨ hb, subset_closure ( by simpa using hbU ) ⟩;
        · refine le_trans (b := diam (closure U))
            (Metric.diam_le_of_forall_dist_le (s := closure U ∩ closure Uᶜ) Metric.diam_nonneg ?_) ?_;
          · exact fun x hx y hy => Metric.dist_le_diam_of_mem ( hU_bdd.closure ) ( by aesop ) ( by aesop );
          · rw [ hab ]

/-- Corollary: diam(U) = diam(frontier U) for bounded open nonempty sets. -/
theorem diam_eq_diam_frontier {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {U : Set E}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) (hU_ne : U.Nonempty) :
    Metric.diam U = Metric.diam (frontier U) := by
  rw [← Metric.diam_closure]
  exact diam_closure_eq_diam_frontier hU_open hU_bdd hU_ne

/-! ## Connected sets have μH[1] ≥ diameter

  For a connected set S in a metric space, the 1-dimensional Hausdorff measure
  is at least the diameter. Proof: project onto the line through any two points
  (using the 1-Lipschitz distance function), apply connectedness to get an interval,
  and use the Lipschitz bound on Hausdorff measure.
-/

/-- For a connected set S in a metric space, μH[1](S) ≥ ediam(S).
    This is a basic result in geometric measure theory. -/
theorem hausdorff_one_ge_ediam_of_isPreconnected {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {S : Set X} (hconn : IsPreconnected S) :
    Metric.ediam S ≤ MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) S := by
  rw [Metric.ediam]
  apply iSup₂_le; intro a ha; apply iSup₂_le; intro b hb
  have hlip : LipschitzWith 1 (dist a : X → ℝ) := LipschitzWith.dist_right a
  have hconn_im : IsPreconnected ((dist a) '' S) := hconn.image _ hlip.continuous.continuousOn
  have h0 : (0 : ℝ) ∈ (dist a) '' S := ⟨a, ha, dist_self a⟩
  have hd : dist a b ∈ (dist a) '' S := ⟨b, hb, rfl⟩
  have hIcc : Set.Icc 0 (dist a b) ⊆ (dist a) '' S := hconn_im.Icc_subset h0 hd
  have hlip_bound : MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) ((dist a) '' S) ≤
      MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) S := by
    calc MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) ((dist a) '' S)
        = MeasureTheory.volume ((dist a) '' S) := by rw [MeasureTheory.hausdorffMeasure_real]
      _ ≤ (1 : NNReal) ^ (1 : ℝ) * MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) S := by
          rw [← MeasureTheory.hausdorffMeasure_real]
          exact hlip.hausdorffMeasure_image_le (by norm_num) S
      _ = MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) S := by simp
  calc edist a b = ENNReal.ofReal (dist a b) := edist_dist a b
    _ = MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) (Set.Icc (0 : ℝ) (dist a b)) := by
          rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]; simp
    _ ≤ MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) ((dist a) '' S) :=
          MeasureTheory.measure_mono hIcc
    _ ≤ MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) S := hlip_bound

end Erdos1044


/-! ### From ComponentRoot.lean -/

/-
  Lemma 4.1: Every connected component of Ω(f) contains a root of f.
  Uses the maximum modulus principle applied to 1/f.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## OmegaSet is bounded for monic polynomials of positive degree -/

/-
For a monic polynomial f of degree ≥ 1, Ω(f) is bounded.
-/
lemma omegaSet_isBounded (f : Polynomial ℂ) (_hf : f.Monic) (hf_deg : f.natDegree ≥ 1) :
    Bornology.IsBounded (OmegaSet f) := by
      -- For a monic polynomial f of degree n ≥ 1, for |z| > R (some R large enough), |f(z)| > 1.
      have h_bound : ∃ R : ℝ, ∀ z : ℂ, ‖z‖ > R → ‖f.eval z‖ > 1 := by
        have h_bound : Filter.Tendsto (fun z : ℂ => ‖f.eval z‖) (Filter.comap (fun z : ℂ => ‖z‖) Filter.atTop) Filter.atTop := by
          apply_rules [ Polynomial.tendsto_norm_atTop ];
          · exact Polynomial.natDegree_pos_iff_degree_pos.mp hf_deg;
          · exact Filter.tendsto_comap;
        have := h_bound.eventually_gt_atTop 1;
        rw [ Filter.eventually_comap ] at this;
        rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ R, hR ⟩ ; exact ⟨ R, fun z hz => hR _ hz.le _ rfl ⟩ ;
      exact isBounded_iff_forall_norm_le.mpr ⟨ h_bound.choose, fun z hz => not_lt.1 fun hlt => not_le_of_gt ( h_bound.choose_spec z hlt ) ( le_of_lt hz ) ⟩

/-! ## Frontier of a maximal connected open subset of an open set
    lies in the complement -/

/-
If U is a maximal preconnected open subset of an open set S,
    then frontier U ⊆ Sᶜ.
-/
lemma frontier_maximal_component_sub_compl
    {S : Set ℂ} (hS : IsOpen S)
    {U : Set ℂ} (hU : IsPreconnected U) (hU_open : IsOpen U)
    (hU_sub : U ⊆ S) (_hU_ne : U.Nonempty)
    (hU_max : ∀ V : Set ℂ, IsPreconnected V → IsOpen V → U ⊆ V → V ⊆ S → V = U) :
    frontier U ⊆ Sᶜ := by
      contrapose! hU_max;
      -- Since $z \in \text{frontier } U \cap S$, there exists an $\epsilon > 0$ such that $B(z, \epsilon) \subseteq S$.
      obtain ⟨z, hz⟩ : ∃ z, z ∈ frontier U ∧ z ∈ S := by
        grind
      obtain ⟨ε, hε_pos, hε⟩ : ∃ ε > 0, Metric.ball z ε ⊆ S := by
        exact Metric.isOpen_iff.mp hS z hz.2;
      -- Since $z \in \text{closure } U$, there exists a point $w \in U$ such that $w \in B(z, \epsilon)$.
      obtain ⟨w, hwU, hwε⟩ : ∃ w ∈ U, w ∈ Metric.ball z ε := by
        exact Exists.elim ( mem_closure_iff_nhds_basis ( Metric.nhds_basis_ball ) |>.1 hz.1.1 ε hε_pos ) fun w hw => ⟨ w, hw.1, hw.2 ⟩;
      refine ⟨ U ∪ Metric.ball z ε, ?_, ?_, ?_, ?_, ?_ ⟩;
      · apply_rules [ IsPreconnected.union, hU ];
        exact convex_ball _ _ |> Convex.isPreconnected;
      · exact IsOpen.union hU_open ( Metric.isOpen_ball );
      · exact Set.subset_union_left;
      · exact Set.union_subset hU_sub hε;
      · simp_all +decide [ Set.ext_iff ];
        exact ⟨ z, by simpa using hε_pos, fun h => hz.1.2 <| mem_interior_iff_mem_nhds.mpr <| hU_open.mem_nhds h ⟩

/-! ## f is nonzero on a component with no roots, and on its frontier -/

/-- If z ∈ frontier U and frontier U ⊆ (OmegaSet f)ᶜ, then ‖f.eval z‖ ≥ 1. -/
lemma norm_eval_ge_one_of_frontier {f : Polynomial ℂ}
    {U : Set ℂ} (hfr : frontier U ⊆ (OmegaSet f)ᶜ)
    {z : ℂ} (hz : z ∈ frontier U) :
    1 ≤ ‖f.eval z‖ := by
  have := hfr hz
  simp only [OmegaSet, mem_compl_iff, mem_setOf_eq, not_lt] at this
  exact this

/-
If f has no root in U and ‖f.eval z‖ ≥ 1 on frontier U,
    then f.eval z ≠ 0 for all z ∈ closure U.
-/
lemma eval_ne_zero_on_closure {f : Polynomial ℂ}
    {U : Set ℂ} (_hU_open : IsOpen U)
    (hno_root : ∀ z ∈ U, ¬f.IsRoot z)
    (hfr : frontier U ⊆ (OmegaSet f)ᶜ) :
    ∀ z ∈ closure U, f.eval z ≠ 0 := by
      rw [ closure_eq_self_union_frontier ];
      simp_all +decide [ OmegaSet ];
      rintro z ( hz | hz ) <;> [ exact hno_root z hz; exact fun h => hfr hz <| by simp +decide [ h ] ]

/-
The reciprocal 1/f is DiffContOnCl on U when f has no zeros on closure U.
-/
lemma diffContOnCl_inv_eval {f : Polynomial ℂ}
    {U : Set ℂ} (_hU_open : IsOpen U)
    (hne : ∀ z ∈ closure U, f.eval z ≠ 0) :
    DiffContOnCl ℂ (fun z => (f.eval z)⁻¹) U := by
      refine ⟨ DifferentiableOn.inv ( ?_ ) ?_, ?_ ⟩;
      · exact f.differentiable.differentiableOn;
      · exact fun x hx => hne x <| subset_closure hx;
      · exact ContinuousOn.inv₀ ( f.continuous.continuousOn ) hne

/-! ## Main theorem: component_contains_root -/

/-
**Lemma 4.1**: Every connected component of Ω(f) contains at least one root of f.

Proof: By contradiction. Suppose U is a maximal preconnected open subset of Ω(f)
with no root of f. Then:
1. U is bounded (since Ω(f) is bounded for monic f of degree ≥ 1).
2. frontier U ⊆ (Ω(f))ᶜ (maximality), so ‖f(z)‖ ≥ 1 on frontier U.
3. f has no zeros on U (by assumption) or on frontier U (by step 2),
   hence f is nonzero on closure U.
4. The function 1/f is DiffContOnCl on U.
5. On frontier U, ‖(f(z))⁻¹‖ ≤ 1.
6. By the maximum modulus principle, ‖(f(z))⁻¹‖ ≤ 1 on closure U,
   hence ‖f(z)‖ ≥ 1 on U.
7. But U ⊆ Ω(f) = {‖f(z)‖ < 1}, contradiction.
-/
theorem component_contains_root (f : Polynomial ℂ) (hf : f.Monic)
    (hf_deg : f.natDegree ≥ 1)
    (U : Set ℂ) (hU : IsPreconnected U) (hU_open : IsOpen U)
    (hU_sub : U ⊆ OmegaSet f) (hU_ne : U.Nonempty)
    (hU_max : ∀ V : Set ℂ, IsPreconnected V → IsOpen V → U ⊆ V → V ⊆ OmegaSet f → V = U) :
    ∃ z ∈ U, f.IsRoot z := by
      by_contra h;
      -- Then $f$ is nonzero on $U$ and on its frontier.
      have h_nonzero : ∀ z ∈ closure U, f.eval z ≠ 0 := by
        apply_rules [ eval_ne_zero_on_closure ];
        · aesop;
        · apply frontier_maximal_component_sub_compl; exact omegaSet_isOpen f; exact hU; exact hU_open; exact hU_sub; exact hU_ne; exact hU_max;
      -- By the maximum modulus principle, ‖(f(z))⁻¹‖ ≤ 1 on closure U.
      have h_max_modulus : ∀ z ∈ closure U, ‖(f.eval z)⁻¹‖ ≤ 1 := by
        apply_rules [ Complex.norm_le_of_forall_mem_frontier_norm_le ];
        · exact omegaSet_isBounded f hf hf_deg |> fun h => h.subset hU_sub;
        · exact diffContOnCl_inv_eval hU_open h_nonzero
        · intro z hz
          have hz_frontier : z ∈ frontier U := hz
          have hz_norm : 1 ≤ ‖f.eval z‖ := by
            apply norm_eval_ge_one_of_frontier;
            exact frontier_maximal_component_sub_compl ( omegaSet_isOpen f ) hU hU_open hU_sub hU_ne hU_max;
            exact hz_frontier
          simp;
          exact inv_le_one_of_one_le₀ hz_norm;
      simp +zetaDelta at *;
      exact absurd ( h_max_modulus _ ( subset_closure hU_ne.choose_spec ) ) ( not_le_of_gt ( one_lt_inv₀ ( norm_pos_iff.mpr ( h _ hU_ne.choose_spec ) ) |>.2 ( hU_sub hU_ne.choose_spec ) ) )

end Erdos1044


/-! ### From BoundaryMeasure.lean -/

/-
  Two-sheet boundary measure bound:
  For a bounded open set U in ℂ, μH[1](frontier U) ≥ 2 · diam(U).
-/

open Set Metric MeasureTheory Topology Complex

noncomputable section

namespace Erdos1044

/-! ## Slice properties of open sets in ℂ -/

private abbrev imSlice (U : Set ℂ) (t : ℝ) : Set ℝ :=
  {y : ℝ | (⟨t, y⟩ : ℂ) ∈ U}

lemma im_slice_isOpen {U : Set ℂ} (hU : IsOpen U) (t : ℝ) :
    IsOpen (imSlice U t) := by
      refine isOpen_iff_forall_mem_open.mpr ?_;
      intro x hx
      obtain ⟨ε, hε⟩ : ∃ ε > 0, Metric.ball (⟨t, x⟩ : ℂ) ε ⊆ U := by
        exact Metric.isOpen_iff.mp hU _ hx;
      refine ⟨ Metric.ball x ε, ?_, Metric.isOpen_ball, ?_ ⟩ <;> simp_all +decide [ Set.subset_def, Complex.dist_eq ];
      exact fun y hy => hε.2 _ <| by simpa [ Complex.normSq, Complex.norm_def ] using Real.sqrt_lt' hε.1 |>.2 <| by nlinarith [ abs_lt.mp hy ] ;

lemma im_slice_bddAbove {U : Set ℂ} (hU : Bornology.IsBounded U) (t : ℝ) :
    BddAbove (imSlice U t) := by
      rcases hU.exists_pos_norm_le with ⟨ M, hM ⟩;
      exact ⟨ M, fun y hy => by have := hM.2 _ hy; exact le_trans ( le_abs_self _ ) ( by simpa [ Complex.norm_def, Complex.normSq ] using Complex.abs_im_le_norm ( ⟨ t, y ⟩ : ℂ ) |> le_trans <| this ) ⟩

lemma im_slice_bddBelow {U : Set ℂ} (hU : Bornology.IsBounded U) (t : ℝ) :
    BddBelow (imSlice U t) := by
      obtain ⟨ M, hM ⟩ := hU.exists_pos_norm_le;
      exact ⟨ -M, fun y hy => neg_le_of_abs_le <| by simpa using hM.2 _ hy |> le_trans ( Complex.abs_im_le_norm _ ) ⟩

lemma slice_inf_not_mem {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (_ht : (imSlice U t).Nonempty) :
    (⟨t, sInf (imSlice U t)⟩ : ℂ) ∉ U := by
      unfold imSlice at *;
      have := Metric.isOpen_iff.mp hU_open;
      contrapose! this;
      use ⟨t, sInf {y | ⟨t, y⟩ ∈ U}⟩;
      simp_all +decide [ Set.not_subset ];
      intro ε ε_pos;
      refine ⟨ ⟨ t, sInf { y | { re := t, im := y } ∈ U } - ε / 2 ⟩, ?_, ?_ ⟩ <;> norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def ];
      · rw [ Real.sqrt_mul_self ] <;> linarith;
      · intro h;
        exact absurd ( csInf_le ( show BddBelow { y : ℝ | { re := t, im := y } ∈ U } from by
                                                              have := hU_bdd.exists_pos_norm_le;
                                                              obtain ⟨ R, R_pos, hR ⟩ := this; exact ⟨ -R, fun y hy => by have := hR _ hy; rw [ Complex.norm_def ] at this; rw [ Real.sqrt_le_left ] at this <;> norm_num [ Complex.normSq ] at * <;> nlinarith ⟩ ; ) h ) ( by linarith )

lemma slice_inf_mem_closure {U : Set ℂ} (_hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (ht : (imSlice U t).Nonempty) :
    (⟨t, sInf (imSlice U t)⟩ : ℂ) ∈ closure U := by
      -- By definition of infimum, there exists a sequence $(y_n)$ in $(imSlice U t)$ such that $y_n \to sInf (imSlice U t)$.
      obtain ⟨y_n, hy_n⟩ : ∃ (y_n : ℕ → ℝ), (∀ n, y_n n ∈ imSlice U t) ∧ Filter.Tendsto y_n Filter.atTop (nhds (sInf (imSlice U t))) := by
        have h_seq : ∀ ε > 0, ∃ y ∈ imSlice U t, |y - sInf (imSlice U t)| < ε := by
          exact fun ε ε_pos => by rcases exists_lt_of_csInf_lt ( ht ) ( lt_add_of_pos_right _ ε_pos ) with ⟨ y, hy, hy' ⟩ ; exact ⟨ y, hy, abs_lt.mpr ⟨ by linarith [ hy', csInf_le ( show BddBelow ( imSlice U t ) from im_slice_bddBelow hU_bdd t ) hy ], by linarith [ hy', csInf_le ( show BddBelow ( imSlice U t ) from im_slice_bddBelow hU_bdd t ) hy ] ⟩ ⟩ ;
        exact ⟨ fun n => Classical.choose ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ), fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1, tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_seq ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
      refine mem_closure_iff_seq_limit.mpr ?_;
      refine ⟨ fun n => ⟨ t, y_n n ⟩, ?_, ?_ ⟩ <;> simp_all +decide [  ];
      rw [ tendsto_iff_norm_sub_tendsto_zero ] at *;
      convert hy_n.2 using 2 ; norm_num [ Complex.normSq, Complex.norm_def ];
      rw [ Real.sqrt_mul_self_eq_abs ]

lemma slice_inf_mem_frontier {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (ht : (imSlice U t).Nonempty) :
    (⟨t, sInf (imSlice U t)⟩ : ℂ) ∈ frontier U := by
  constructor
  · exact slice_inf_mem_closure hU_open hU_bdd ht
  · simp only [hU_open.interior_eq]
    exact slice_inf_not_mem hU_open hU_bdd ht

lemma slice_sup_not_mem {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (_ht : (imSlice U t).Nonempty) :
    (⟨t, sSup (imSlice U t)⟩ : ℂ) ∉ U := by
      intro h;
      obtain ⟨ ε, ε_pos, hε ⟩ := Metric.isOpen_iff.mp hU_open _ h;
      -- Consider the point $(t, sSup (imSlice U t) + \frac{\epsilon}{2})$.
      have h_point : (⟨t, sSup (imSlice U t) + ε / 2⟩ : ℂ) ∈ U := by
        refine hε ?_;
        norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def ];
        rw [ Real.sqrt_mul_self ] <;> linarith;
      exact absurd ( le_csSup ( show BddAbove ( imSlice U t ) from im_slice_bddAbove hU_bdd t ) <| show sSup ( imSlice U t ) + ε / 2 ∈ imSlice U t from h_point ) ( by linarith )

lemma slice_sup_mem_closure {U : Set ℂ} (_hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (ht : (imSlice U t).Nonempty) :
    (⟨t, sSup (imSlice U t)⟩ : ℂ) ∈ closure U := by
      -- By definition of $sSup$, there exists a sequence $(y_n)$ in $imSlice U t$ such that $y_n \to sSup (imSlice U t)$.
      obtain ⟨y_n, hy_n⟩ : ∃ y_n : ℕ → ℝ, (∀ n, y_n n ∈ imSlice U t) ∧ Filter.Tendsto y_n Filter.atTop (nhds (sSup (imSlice U t))) := by
        have h_seq : ∀ ε > 0, ∃ y ∈ imSlice U t, sSup (imSlice U t) - ε < y ∧ y ≤ sSup (imSlice U t) := by
          exact fun ε ε_pos => by rcases exists_lt_of_lt_csSup ht ( sub_lt_self _ ε_pos ) with ⟨ y, hy₁, hy₂ ⟩ ; exact ⟨ y, hy₁, hy₂, le_csSup ( show BddAbove ( imSlice U t ) from im_slice_bddAbove hU_bdd t ) hy₁ ⟩ ;
        choose! y hy using h_seq;
        exact ⟨ fun n => y ( 1 / ( n + 1 ) ), fun n => hy _ ( by positivity ) |>.1, tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero ( fun _ => abs_nonneg _ ) ( fun n => abs_le.mpr ⟨ by linarith [ hy ( 1 / ( n + 1 ) ) ( by positivity ) ], by linarith [ hy ( 1 / ( n + 1 ) ) ( by positivity ) ] ⟩ ) <| tendsto_one_div_add_atTop_nhds_zero_nat ⟩;
      -- Since $y_n \to sSup (imSlice U t)$, we have $⟨t, y_n⟩ \to ⟨t, sSup (imSlice U t)⟩$.
      have h_seq : Filter.Tendsto (fun n => ⟨t, y_n n⟩ : ℕ → ℂ) Filter.atTop (nhds ⟨t, sSup (imSlice U t)⟩) := by
        rw [ tendsto_iff_norm_sub_tendsto_zero ] at *;
        simp_all +decide [ Complex.normSq, Complex.norm_def ];
        simpa [ Real.sqrt_mul_self_eq_abs ] using hy_n.2;
      exact mem_closure_of_tendsto h_seq ( Filter.Eventually.of_forall fun n => hy_n.1 n )

lemma slice_sup_mem_frontier {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (ht : (imSlice U t).Nonempty) :
    (⟨t, sSup (imSlice U t)⟩ : ℂ) ∈ frontier U := by
  constructor
  · exact slice_sup_mem_closure hU_open hU_bdd ht
  · simp only [hU_open.interior_eq]
    exact slice_sup_not_mem hU_open hU_bdd ht

lemma slice_inf_lt_sup {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {t : ℝ} (ht : (imSlice U t).Nonempty) :
    sInf (imSlice U t) < sSup (imSlice U t) := by
      obtain ⟨ x, hx ⟩ := ht;
      obtain ⟨ ε, ε_pos, hε ⟩ := Metric.isOpen_iff.mp ( im_slice_isOpen hU_open t ) x hx;
      refine lt_of_le_of_lt ( csInf_le ?_ ( hε ( Metric.mem_ball_self ε_pos ) ) ) ?_;
      · exact im_slice_bddBelow hU_bdd t;
      · exact lt_of_lt_of_le ( show x < x + ε / 2 by linarith ) ( le_csSup ( show BddAbove ( imSlice U t ) from im_slice_bddAbove hU_bdd t ) ( hε ( Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith, by linarith ⟩ ) ) )

/-! ## Bottom and top boundary sets (original definitions, kept for reference) -/

def bottomBdry (U : Set ℂ) : Set ℂ :=
  {z | z.re ∈ re '' U ∧ z ∈ frontier U ∧
       z.im = sInf (imSlice U z.re)}

def topBdry (U : Set ℂ) : Set ℂ :=
  {z | z.re ∈ re '' U ∧ z ∈ frontier U ∧
       z.im = sSup (imSlice U z.re)}

lemma bottomBdry_subset_frontier {U : Set ℂ} : bottomBdry U ⊆ frontier U :=
  fun _ h => h.2.1

lemma topBdry_subset_frontier {U : Set ℂ} : topBdry U ⊆ frontier U :=
  fun _ h => h.2.1

lemma bottomBdry_disjoint_topBdry {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) :
    Disjoint (bottomBdry U) (topBdry U) := by
  rw [Set.disjoint_iff]
  intro z ⟨hb, ht⟩
  have hne : (imSlice U z.re).Nonempty := by
    obtain ⟨w, hw, hrw⟩ := hb.1
    exact ⟨w.im, by change (⟨z.re, w.im⟩ : ℂ) ∈ U; rwa [← hrw, Complex.eta]⟩
  linarith [slice_inf_lt_sup hU_open hU_bdd hne, hb.2.2, ht.2.2]

lemma re_surj_bottomBdry {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) :
    re '' U ⊆ re '' (bottomBdry U) := by
  intro t ⟨z, hz, hzt⟩
  have hne : (imSlice U t).Nonempty :=
    ⟨z.im, by change (⟨t, z.im⟩ : ℂ) ∈ U; rwa [← hzt, Complex.eta]⟩
  exact ⟨⟨t, sInf (imSlice U t)⟩,
    ⟨⟨z, hz, hzt⟩, slice_inf_mem_frontier hU_open hU_bdd hne, by simp⟩, by simp⟩

lemma re_surj_topBdry {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) :
    re '' U ⊆ re '' (topBdry U) := by
  intro t ⟨z, hz, hzt⟩
  have hne : (imSlice U t).Nonempty :=
    ⟨z.im, by change (⟨t, z.im⟩ : ℂ) ∈ U; rwa [← hzt, Complex.eta]⟩
  exact ⟨⟨t, sSup (imSlice U t)⟩,
    ⟨⟨z, hz, hzt⟩, slice_sup_mem_frontier hU_open hU_bdd hne, by simp⟩, by simp⟩

/-! ## Hausdorff measure bounds -/

lemma re_lipschitz : LipschitzWith 1 (re : ℂ → ℝ) :=
  LipschitzWith.of_dist_le_mul (fun x y => by
    simp [Complex.dist_eq, Real.dist_eq]
    exact Complex.abs_re_le_norm (x - y))

lemma hausdorff_ge_of_re_surj {A : Set ℂ} {I : Set ℝ}
    (hAI : I ⊆ re '' A) :
    μH[1] I ≤ μH[1] A := by
  calc μH[1] I ≤ μH[1] (re '' A) := measure_mono hAI
    _ ≤ (1 : NNReal) ^ (1 : ℝ) * μH[1] A :=
        re_lipschitz.hausdorffMeasure_image_le (by norm_num : (0:ℝ) ≤ 1) A
    _ = μH[1] A := by simp

/-! ## Measurable decomposition of the frontier -/

/-- The set of points below which the vertical line through them does not intersect U. -/
private def lowSet (U : Set ℂ) : Set ℂ :=
  {z : ℂ | ∀ y : ℝ, y < z.im → (⟨z.re, y⟩ : ℂ) ∉ U}

/-- The set of points above which the vertical line through them does not intersect U. -/
private def highSet (U : Set ℂ) : Set ℂ :=
  {z : ℂ | ∀ y : ℝ, y > z.im → (⟨z.re, y⟩ : ℂ) ∉ U}

/-
lowSet U is closed when U is open, because its complement is open.
-/
lemma lowSet_isClosed {U : Set ℂ} (hU : IsOpen U) : IsClosed (lowSet U) := by
  refine isClosed_iff_clusterPt.mpr ?_;
  intro a ha; by_contra h; simp_all +decide [ lowSet ] ;
  rcases h with ⟨ x, hx₁, hx₂ ⟩ ; rcases Metric.mem_nhds_iff.1 ( hU.mem_nhds hx₂ ) with ⟨ ε, εpos, hε ⟩ ; simp_all +decide  ;
  -- Choose δ = min(ε, (a.im - x) / 2).
  set δ := min ε ((a.im - x) / 2) with hδ;
  -- Since $a$ is a cluster point of the complement of $lowSet U$, there exists a point $z$ in the neighborhood of $a$ such that $z$ is not in $lowSet U$.
  obtain ⟨ z, hz₁, hz₂ ⟩ : ∃ z ∈ Metric.ball a δ, ∀ y : ℝ, y < z.im → (⟨z.re, y⟩ : ℂ) ∉ U := by
    rw [ clusterPt_principal_iff ] at ha;
    exact ha _ ( Metric.ball_mem_nhds _ <| lt_min εpos <| half_pos <| sub_pos.mpr hx₁ ) |> fun ⟨ z, hz₁, hz₂ ⟩ => ⟨ z, hz₁, hz₂ ⟩;
  refine hz₂ x ?_ ?_;
  · simp_all +decide [ Complex.dist_eq, Complex.normSq, Complex.norm_def ];
    nlinarith [ Real.sqrt_nonneg ( ( z.re - a.re ) * ( z.re - a.re ) + ( z.im - a.im ) * ( z.im - a.im ) ), Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg ( z.re - a.re ) ) ( mul_self_nonneg ( z.im - a.im ) ) ) ];
  · refine hε ?_;
    simp_all +decide [ Complex.dist_eq, Complex.normSq, Complex.norm_def ];
    exact lt_of_le_of_lt ( Real.sqrt_le_sqrt <| by nlinarith ) hz₁.1

/-
highSet U is closed when U is open.
-/
lemma highSet_isClosed {U : Set ℂ} (hU : IsOpen U) : IsClosed (highSet U) := by
  unfold highSet;
  simp +decide only [setOf_forall];
  refine isClosed_iInter fun i => ?_;
  rw [ show { x : ℂ | i > x.im → { re := x.re, im := i } ∉ U } = { x : ℂ | i ≤ x.im } ∪ { x : ℂ | { re := x.re, im := i } ∉ U } by ext; by_cases hi : i ≤ ‹ℂ›.im <;> aesop ];
  refine IsClosed.union ?_ ?_;
  · exact isClosed_le continuous_const Complex.continuous_im;
  · refine isClosed_compl_iff.mpr ?_;
    convert hU.preimage ( show Continuous fun x : ℂ => { re := x.re, im := i } from ?_ ) using 1;
    norm_num [ Complex.mk_eq_add_mul_I ];
    fun_prop

/-- The lower frontier: points on frontier U that are at the bottom of the vertical slice. -/
private def lowerFrontier (U : Set ℂ) : Set ℂ :=
  frontier U ∩ lowSet U ∩ re ⁻¹' (re '' U)

/-- The upper frontier: points on frontier U that are at the top of the vertical slice. -/
private def upperFrontier (U : Set ℂ) : Set ℂ :=
  frontier U ∩ highSet U ∩ re ⁻¹' (re '' U)

lemma lowerFrontier_subset_frontier {U : Set ℂ} : lowerFrontier U ⊆ frontier U :=
  fun _ h => h.1.1

lemma upperFrontier_subset_frontier {U : Set ℂ} : upperFrontier U ⊆ frontier U :=
  fun _ h => h.1.1

/-- The infimum point of a slice is in the lowSet. -/
lemma slice_inf_mem_lowSet {U : Set ℂ} {t : ℝ} (_ht : (imSlice U t).Nonempty)
    (hbdd : BddBelow (imSlice U t)) :
    (⟨t, sInf (imSlice U t)⟩ : ℂ) ∈ lowSet U := by
  intro y hy hmem
  exact absurd (csInf_le hbdd hmem) (not_le.mpr hy)

/-- The supremum point of a slice is in the highSet. -/
lemma slice_sup_mem_highSet {U : Set ℂ} {t : ℝ} (_ht : (imSlice U t).Nonempty)
    (hbdd : BddAbove (imSlice U t)) :
    (⟨t, sSup (imSlice U t)⟩ : ℂ) ∈ highSet U := by
  intro y hy hmem
  exact absurd (le_csSup hbdd hmem) (not_le.mpr hy)

/-- re '' U is open when U is open. -/
lemma re_image_isOpen {U : Set ℂ} (hU : IsOpen U) : IsOpen (re '' U) :=
  Complex.isOpenMap_re U hU

/-- lowerFrontier U is a MeasurableSet (it's a Borel set: intersection of closed, closed, and open). -/
lemma lowerFrontier_measurableSet {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet (lowerFrontier U) := by
  apply MeasurableSet.inter
  · exact MeasurableSet.inter isClosed_frontier.measurableSet (lowSet_isClosed hU).measurableSet
  · exact (re_image_isOpen hU).preimage Complex.continuous_re |>.measurableSet

/-- upperFrontier U is a MeasurableSet. -/
lemma upperFrontier_measurableSet {U : Set ℂ} (hU : IsOpen U) :
    MeasurableSet (upperFrontier U) := by
  apply MeasurableSet.inter
  · exact MeasurableSet.inter isClosed_frontier.measurableSet (highSet_isClosed hU).measurableSet
  · exact (re_image_isOpen hU).preimage Complex.continuous_re |>.measurableSet

/-- The lowerFrontier projects surjectively onto re '' U. -/
lemma re_surj_lowerFrontier {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) :
    re '' U ⊆ re '' (lowerFrontier U) := by
  intro t ⟨z, hz, hzt⟩
  have hne : (imSlice U t).Nonempty :=
    ⟨z.im, by change (⟨t, z.im⟩ : ℂ) ∈ U; rwa [← hzt, Complex.eta]⟩
  refine ⟨⟨t, sInf (imSlice U t)⟩, ?_, by simp⟩
  refine ⟨⟨slice_inf_mem_frontier hU_open hU_bdd hne,
    slice_inf_mem_lowSet hne (im_slice_bddBelow hU_bdd t)⟩, ?_⟩
  exact ⟨z, hz, hzt⟩

/-- The upperFrontier projects surjectively onto re '' U. -/
lemma re_surj_upperFrontier {U : Set ℂ} (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) :
    re '' U ⊆ re '' (upperFrontier U) := by
  intro t ⟨z, hz, hzt⟩
  have hne : (imSlice U t).Nonempty :=
    ⟨z.im, by change (⟨t, z.im⟩ : ℂ) ∈ U; rwa [← hzt, Complex.eta]⟩
  refine ⟨⟨t, sSup (imSlice U t)⟩, ?_, by simp⟩
  refine ⟨⟨slice_sup_mem_frontier hU_open hU_bdd hne,
    slice_sup_mem_highSet hne (im_slice_bddAbove hU_bdd t)⟩, ?_⟩
  exact ⟨z, hz, hzt⟩

/-
lowerFrontier and upperFrontier are disjoint.
-/
lemma lowerFrontier_disjoint_upperFrontier {U : Set ℂ}
    (hU_open : IsOpen U) :
    Disjoint (lowerFrontier U) (upperFrontier U) := by
      unfold lowerFrontier upperFrontier; simp +decide [ Set.disjoint_left ] ;
      intro z hz₁ hz₂ x hx₁ hx₂ hz₃ hz₄ y hy₁ hy₂; have := hz₂ ( y.im ) ; have := hz₄ ( y.im ) ; simp_all +decide  ;
      cases lt_trichotomy y.im z.im <;> simp_all +decide [ Complex.mk_eq_add_mul_I ];
      · exact this ( by convert hy₁ using 1; simp +decide [ Complex.ext_iff, hy₂ ] );
      · cases ‹_› <;> simp_all +decide ;
        · simp_all +decide [ lowSet, highSet, frontier_eq_closure_inter_closure ];
          exact hz₃.2 ( by convert hy₁ using 1; simp +decide [ *, Complex.ext_iff ] );
        · exact this ( by convert hy₁ using 1; simp +decide [ Complex.ext_iff, * ] )

/-- The main two-sheet bound for the Re direction. -/
theorem frontier_hausdorff_ge_two_re_measure {U : Set ℂ}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) (_hU_ne : U.Nonempty) :
    2 * μH[1] (re '' U) ≤ μH[1] (frontier U) := by
  have hL := lowerFrontier_measurableSet hU_open
  have hDisj := lowerFrontier_disjoint_upperFrontier hU_open
  have hUnion_sub : lowerFrontier U ∪ upperFrontier U ⊆ frontier U :=
    Set.union_subset lowerFrontier_subset_frontier upperFrontier_subset_frontier
  calc 2 * μH[1] (re '' U)
      = μH[1] (re '' U) + μH[1] (re '' U) := by ring
    _ ≤ μH[1] (lowerFrontier U) + μH[1] (upperFrontier U) := by
        gcongr
        · exact hausdorff_ge_of_re_surj (re_surj_lowerFrontier hU_open hU_bdd)
        · exact hausdorff_ge_of_re_surj (re_surj_upperFrontier hU_open hU_bdd)
    _ = μH[1] (lowerFrontier U ∪ upperFrontier U) := by
        rw [measure_union' hDisj hL]
    _ ≤ μH[1] (frontier U) := measure_mono hUnion_sub

/-- Multiplication by a unit complex number is an isometry. -/
lemma isometry_mul_unit (a : ℂ) (ha : ‖a‖ = 1) :
    Isometry (fun z => a * z) :=
  isometry_iff_dist_eq.mpr (fun x y => by
    simp [dist_eq_norm, ← mul_sub, ha])

/-
For any z, w ∈ U (open bounded connected), 2 · edist z w ≤ μH[1](frontier U).
    Proof by rotating U to align z-w with the real axis and applying the two-sheet bound.
-/
lemma frontier_hausdorff_ge_two_edist_pair {U : Set ℂ}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    (hU_conn : IsConnected U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    2 * edist z w ≤ μH[1] (frontier U) := by
      -- Let $a := (starRingEnd ℂ (z - w)) / ‖z - w‖$ (unit rotation aligning $z-w$ with real axis).
      obtain ⟨a, ha⟩ : ∃ a : ℂ, ‖a‖ = 1 ∧ (a * (z - w)).re = ‖z - w‖ := by
        by_cases h : z = w <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
        · exact ⟨ 1, by norm_num ⟩;
        · refine ⟨ ⟨ ( z.re - w.re ) / Real.sqrt ( ( z.re - w.re ) * ( z.re - w.re ) + ( z.im - w.im ) * ( z.im - w.im ) ), - ( z.im - w.im ) / Real.sqrt ( ( z.re - w.re ) * ( z.re - w.re ) + ( z.im - w.im ) * ( z.im - w.im ) ) ⟩, ?_, ?_ ⟩ <;> norm_num [ Complex.normSq, Complex.norm_def ];
          · rw [ div_mul_div_comm, div_mul_div_comm, ← add_div, div_eq_iff ] <;> nlinarith [ Real.mul_self_sqrt ( add_nonneg ( mul_self_nonneg ( z.re - w.re ) ) ( mul_self_nonneg ( z.im - w.im ) ) ), show 0 < ( z.re - w.re ) * ( z.re - w.re ) + ( z.im - w.im ) * ( z.im - w.im ) from not_le.mp fun h' => h <| by refine Complex.ext ?_ ?_ <;> nlinarith ];
          · grind;
      -- Let $V := (fun x => a * x) '' U$. Then:
      set V := (fun x => a * x) '' U with hV_def
      have hV_open : IsOpen V := by
        convert Homeomorph.isOpenMap ( Homeomorph.mulLeft₀ a ( by aesop_cat ) ) U hU_open using 1
      have hV_bdd : Bornology.IsBounded V := by
        rw [ isBounded_iff_forall_norm_le ] at *;
        aesop
      have hV_ne : V.Nonempty := by
        exact ⟨ _, ⟨ z, hz, rfl ⟩ ⟩
      have ha_z_in_V : a * z ∈ V := by
        exact Set.mem_image_of_mem _ hz
      have ha_w_in_V : a * w ∈ V := by
        exact Set.mem_image_of_mem _ hw
      have hV_frontier : frontier V = (fun x => a * x) '' frontier U := by
        by_cases ha : a = 0 <;> simp_all +decide [ mul_comm a ];
        have := Homeomorph.image_frontier ( Homeomorph.mulRight₀ a ha ) U; aesop;
      have hV_measure : μH[1] (frontier V) = μH[1] (frontier U) := by
        grind +suggestions;
      -- Apply frontier_hausdorff_ge_two_re_measure to V:
      have hV_bound : 2 * μH[1] (re '' V) ≤ μH[1] (frontier V) := by
        exact frontier_hausdorff_ge_two_re_measure hV_open hV_bdd hV_ne;
      -- Since $a * z, a * w \in V$ and $V$ is open (hence connected image $re '' V$ is open in ℝ, and connected since $U$ is connected), $re '' V$ contains both $re(a * z)$ and $re(a * w)$, and being a connected open subset of ℝ, it contains the interval between them.
      have hV_re_interval : Set.Icc (min (re (a * z)) (re (a * w))) (max (re (a * z)) (re (a * w))) ⊆ re '' V := by
        have hV_re_connected : IsConnected (re '' V) := by
          apply_rules [ IsConnected.image, hU_conn ];
          · exact continuousOn_const.mul continuousOn_id;
          · exact Complex.continuous_re.continuousOn;
        cases le_total ( a * z |> Complex.re ) ( a * w |> Complex.re ) <;> simp_all +decide ;
        · exact hV_re_connected.Icc_subset ( Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hz ) ( Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hw );
        · exact hV_re_connected.Icc_subset ( Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hw ) ( Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hz );
      -- So, μH[1](re '' V) ≥ |re(a*z) - re(a*w)| = |re(a*(z-w))| = ‖z-w‖ = dist(z,w).
      have hV_re_measure : μH[1] (re '' V) ≥ ENNReal.ofReal (|re (a * z) - re (a * w)|) := by
        refine le_trans ?_ ( MeasureTheory.measure_mono hV_re_interval );
        simp +decide [ Real.volume_Icc ];
        cases max_cases ( a.re * z.re - a.im * z.im ) ( a.re * w.re - a.im * w.im ) <;> cases min_cases ( a.re * z.re - a.im * z.im ) ( a.re * w.re - a.im * w.im ) <;> cases abs_cases ( a.re * z.re - a.im * z.im - ( a.re * w.re - a.im * w.im ) ) <;> linarith;
      simp_all +decide [ mul_sub ];
      exact le_trans ( by
        simpa [edist_dist, Complex.dist_eq] using
          (mul_le_mul_right hV_re_measure (2 : ENNReal)) ) hV_bound

/-- The full two-sheet bound: μH[1](frontier U) ≥ 2 · ediam U.
    Requires connectedness (the statement is false for disconnected sets). -/
theorem frontier_hausdorff_ge_two_ediam {U : Set ℂ}
    (hU_open : IsOpen U) (hU_bdd : Bornology.IsBounded U) (_hU_ne : U.Nonempty)
    (hU_conn : IsConnected U) :
    2 * Metric.ediam U ≤ μH[1] (frontier U) := by
  rw [Metric.ediam]
  rw [show (2 : ENNReal) * (⨆ x ∈ U, ⨆ y ∈ U, edist x y) =
      ⨆ x ∈ U, ⨆ y ∈ U, 2 * edist x y from by
    simp_rw [ENNReal.mul_iSup]]
  exact iSup₂_le fun x hx => iSup₂_le fun y hy =>
    frontier_hausdorff_ge_two_edist_pair hU_open hU_bdd hU_conn hx hy

end Erdos1044


/-! ### From PommerenkeDiam.lean -/

/-
  Helper lemmas for Pommerenke's diameter theorem.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Key helper: norm of f equals 1 on frontier of component -/

/-
On the frontier of a connected component of OmegaSet f (for admissible f of degree ≥ 1),
    the norm ‖f.eval w‖ equals exactly 1.
-/
lemma norm_eval_eq_one_on_frontier (f : Polynomial ℂ) (_hf : IsAdmissible f)
    (_hdeg : f.natDegree ≥ 1)
    {z₀ : ℂ} (hz₀ : z₀ ∈ OmegaSet f)
    {w : ℂ} (hw : w ∈ frontier (connectedComponentIn (OmegaSet f) z₀)) :
    ‖f.eval w‖ = 1 := by
      refine le_antisymm ?_ ?_;
      · -- By definition of frontier, we know that $w \in \overline{\text{component}}$.
        have hw_closure : w ∈ closure (connectedComponentIn (OmegaSet f) z₀) := by
          exact hw.1;
        rw [ mem_closure_iff_seq_limit ] at hw_closure;
        obtain ⟨ x, hx₁, hx₂ ⟩ := hw_closure; exact le_of_tendsto' ( Filter.Tendsto.norm ( f.continuous.continuousAt.tendsto.comp hx₂ ) ) fun n => le_of_lt <| by simpa using ( show ‖f.eval ( x n )‖ < 1 from by simpa using ( show x n ∈ OmegaSet f from by exact connectedComponentIn_subset _ _ <| hx₁ n ) ) ;
      · apply_rules [ norm_eval_ge_one_of_frontier, frontier_maximal_component_sub_compl ];
        exact omegaSet_isOpen f
        · exact isPreconnected_connectedComponentIn;
        · exact IsOpen.connectedComponentIn ( omegaSet_isOpen f );
        · exact connectedComponentIn_subset _ _;
        · exact ⟨ z₀, mem_connectedComponentIn ( by aesop ) ⟩;
        · intro V hV₁ hV₂ hV₃ hV₄;
          refine Set.Subset.antisymm ?_ hV₃;
          grind +suggestions

/-! ## Product of norms: if nonempty product of nonneg reals = 1, some factor ≥ 1 -/

/-
If a nonempty product of nonneg reals equals 1, some element is ≥ 1.
-/
lemma exists_ge_one_of_prod_eq_one {s : Multiset ℝ} (hs_ne : s ≠ ∅)
    (hs_nonneg : ∀ x ∈ s, (0 : ℝ) ≤ x) (hprod : s.prod = 1) :
    ∃ x ∈ s, (1 : ℝ) ≤ x := by
      contrapose! hprod;
      have h_prod_lt_one : ∀ {s : Multiset ℝ}, s ≠ ∅ → (∀ x ∈ s, 0 ≤ x ∧ x < 1) → s.prod < 1 := by
        intros s hs_ne hs_bounds; induction s using Multiset.induction <;> simp_all +decide [ Multiset.prod_cons ] ;
        rename_i k hk;
        by_cases hk_zero : k = 0 <;> simp_all +decide;
        nlinarith [ show 0 ≤ k.prod from Multiset.prod_nonneg fun x hx => hs_bounds.2 x hx |>.1 ];
      exact ne_of_lt ( h_prod_lt_one hs_ne fun x hx => ⟨ hs_nonneg x hx, hprod x hx ⟩ )

/-! ## Diameter strict bound from interior point -/

/-
If U is open and bounded, z ∈ U, w ∈ closure U with dist z w ≥ d > 0,
    then Metric.diam U > d.
-/
lemma diam_gt_of_interior_closure_dist {U : Set ℂ}
    (hU : IsOpen U) (hU_bdd : Bornology.IsBounded U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ closure U)
    {d : ℝ} (hd : d ≤ dist z w) (_hd_pos : 0 < d) :
    d < Metric.diam U := by
      obtain ⟨ ε, ε_pos, hε ⟩ := Metric.isOpen_iff.mp hU z hz;
      -- Choose a point $z'$ in the ball around $z$ with radius $\epsilon$ such that $dist(z', w) > dist(z, w)$.
      obtain ⟨z', hz'⟩ : ∃ z' ∈ ball z ε, dist z' w > dist z w := by
        by_cases hzw : z = w;
        · exact ⟨ z + ε / 2, by simpa [ abs_of_pos ε_pos ] using by linarith, by simpa [ hzw, abs_of_pos ε_pos ] using by linarith ⟩;
        · refine ⟨ z + ( ε / 2 ) * ( z - w ) / ‖z - w‖, ?_, ?_ ⟩ <;> norm_num [ hzw, dist_eq_norm ];
          · rw [ mul_div_cancel_right₀ _ ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr hzw ) ) ] ; linarith [ abs_of_pos ε_pos ];
          · rw [ show z + ↑ε / 2 * ( z - w ) / ↑‖z - w‖ - w = ( z - w ) * ( 1 + ↑ε / 2 / ↑‖z - w‖ ) by ring, norm_mul ];
            norm_cast;
            exact lt_mul_of_one_lt_right ( norm_pos_iff.mpr ( sub_ne_zero.mpr hzw ) ) ( by rw [ Real.norm_of_nonneg ( by positivity ) ] ; nlinarith [ norm_pos_iff.mpr ( sub_ne_zero.mpr hzw ), div_mul_cancel₀ ( ε / 2 ) ( norm_ne_zero_iff.mpr ( sub_ne_zero.mpr hzw ) ) ] );
      -- Since $z' \in U$ and $w \in \overline{U}$, we have $dist(z', w) \leq \text{diam}(U)$.
      have h_dist_le_diam : dist z' w ≤ Metric.diam U := by
        have h_dist_le_diam : ∀ x y : ℂ, x ∈ closure U → y ∈ closure U → dist x y ≤ Metric.diam U := by
          intros x y hx hy;
          rw [ Metric.mem_closure_iff ] at hx hy;
          exact le_of_forall_pos_le_add fun ε ε_pos => by rcases hx ( ε / 2 ) ( half_pos ε_pos ) with ⟨ x', hx', hx'' ⟩ ; rcases hy ( ε / 2 ) ( half_pos ε_pos ) with ⟨ y', hy', hy'' ⟩ ; linarith [ dist_triangle4_right x y x' y', show dist x' y' ≤ diam U from Metric.dist_le_diam_of_mem hU_bdd hx' hy' ] ;
        exact h_dist_le_diam _ _ ( subset_closure ( hε hz'.1 ) ) hw;
      linarith

/-! ## Roots are in OmegaSet -/

/-- Every root of a polynomial is in OmegaSet. -/
lemma root_mem_omegaSet {f : Polynomial ℂ} {z : ℂ} (hz : f.IsRoot z) :
    z ∈ OmegaSet f := by
  simp [OmegaSet, Polynomial.IsRoot.def.mp hz]

/-! ## Closure of component ∩ open set = component -/

/-
For an open set S, if z ∈ closure(connectedComponentIn S z₀) ∩ S,
    then z ∈ connectedComponentIn S z₀.
-/
lemma mem_connectedComponentIn_of_mem_closure_inter {S : Set ℂ} (_hS : IsOpen S)
    {z₀ z : ℂ} (hz₀ : z₀ ∈ S) (hz_closure : z ∈ closure (connectedComponentIn S z₀))
    (hz_S : z ∈ S) :
    z ∈ connectedComponentIn S z₀ := by
      rw [ connectedComponentIn ] at *;
      -- Since the connected component is closed in S, its closure is itself.
      have h_closed : IsClosed (connectedComponent ⟨z₀, hz₀⟩ : Set (↥S)) := by
        exact isClosed_connectedComponent;
      convert h_closed.closure_subset_iff.mpr _ _;
      rotate_left;
      exact connectedComponent ⟨ z₀, hz₀ ⟩;
      exact Set.Subset.rfl;
      exact ⟨ z, hz_S ⟩;
      · grind +suggestions;
      · grind

end Erdos1044


/-! ### From ModelPolyHelpers.lean -/

/-
  Helper lemmas for the model polynomial z^n - 1 and lemniscate structure.
  These are structural results needed for `modelPoly_boundary_length`.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Basic properties of the model polynomial -/

lemma modelPoly_monic (n : ℕ) (hn : n ≥ 1) : (modelPoly n).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by omega)

lemma modelPoly_natDegree (n : ℕ) (_hn : n ≥ 1) : (modelPoly n).natDegree = n :=
  Polynomial.natDegree_X_pow_sub_C

lemma modelPoly_isAdmissible (n : ℕ) (hn : n ≥ 1) : IsAdmissible (modelPoly n) := by
  refine ⟨modelPoly_monic n hn, ?_⟩
  intro z hz
  have hroot : z ^ n = 1 := by
    have : Polynomial.eval z (modelPoly n) = 0 := hz
    simp [modelPoly] at this
    linear_combination this
  have : ‖z‖ ^ n = 1 := by
    rw [← norm_pow, hroot, norm_one]
  exact le_of_eq (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega) |>.mp this)

/-- The omega set of z^n - 1 is {z : ‖z^n - 1‖ < 1}. -/
lemma omegaSet_modelPoly (n : ℕ) :
    OmegaSet (modelPoly n) = {z : ℂ | ‖z ^ n - 1‖ < 1} := by
  ext z; simp [OmegaSet, modelPoly]


end Erdos1044


/-! ### From ArcLengthHelpers.lean -/

/-
  Helper lemmas for the arc-length formula.

  Key results:
  1. `hausdorffMeasure_connected_ge_edist` — μH[1](C) ≥ edist(x,y)
     for connected C in a normed space containing x, y.
  2. `ediam_curve_image_le_integral` — diameter bound on curve images.
-/

open MeasureTheory Topology Set Metric Filter

noncomputable section

namespace Erdos1044

/-! ## Connected sets have large Hausdorff 1-measure -/

/-
For a preconnected set C in a normed space (with Borel σ-algebra),
    μH[1](C) ≥ edist(x, y) for any x, y ∈ C.

    Proof: Let φ(z) = dist(z, x). Then φ is 1-Lipschitz, so
    μH[1](φ '' C) ≤ μH[1](C). Since C is connected and contains x, y,
    φ(C) is a connected subset of ℝ containing 0 and dist(x,y),
    hence [0, dist(x,y)] ⊆ φ(C). Since μH[1] = volume on ℝ,
    μH[1](φ(C)) ≥ volume([0, dist(x,y)]) = dist(x,y) = edist(x,y)
    (the last step uses that dist = edist.toReal for finite distances).
-/
lemma hausdorffMeasure_connected_ge_edist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {C : Set E} (hC : IsPreconnected C)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    edist x y ≤ μH[(1 : ℝ)] C := by
  -- Let φ(z) = dist(z, x). Then φ is 1-Lipschitz, so μH[1](φ '' C) ≤ μH[1](C).
  have h_lip : MeasureTheory.Measure.hausdorffMeasure 1 (Set.image (fun z => dist z x) C) ≤ MeasureTheory.Measure.hausdorffMeasure 1 C := by
    have h_lip : LipschitzWith 1 (fun z => dist z x) := by
      exact LipschitzWith.dist_left x
    generalize_proofs at *; (
    have := h_lip.hausdorffMeasure_image_le ( by norm_num : ( 0 : ℝ ) ≤ 1 ) C
    aesop)
  generalize_proofs at *; (
  -- Since φ(C) is a connected subset of ℝ containing φ(x) = 0 and φ(y) = dist(y, x) = dist(x, y), it must contain the interval [0, dist(x,y)].
  have h_interval : Set.Icc 0 (dist y x) ⊆ Set.image (fun z => dist z x) C := by
    have h_image : IsPreconnected (Set.image (fun z => dist z x) C) := by
      exact hC.image _ ( continuous_id.dist continuous_const |> Continuous.continuousOn )
    generalize_proofs at *; (
    exact h_image.Icc_subset ( Set.mem_image_of_mem _ hx ) ( Set.mem_image_of_mem _ hy ) |> fun h => h.trans' ( Set.Icc_subset_Icc ( by simp +decide ) le_rfl ))
  generalize_proofs at *; (
  -- Since μH[1] on ℝ equals volume, we have μH[1](φ(C)) ≥ μH[1](Icc 0 (dist x y)).
  have h_volume : MeasureTheory.Measure.hausdorffMeasure 1 (Set.image (fun z => dist z x) C) ≥ MeasureTheory.Measure.hausdorffMeasure 1 (Set.Icc 0 (dist y x)) := by
    exact MeasureTheory.measure_mono h_interval
  generalize_proofs at *; (
  simp_all +decide [ edist_dist, dist_comm ];
  exact h_volume.trans h_lip)))

/-! ## Diameter bound for curve images -/

/-
The ediam of the image of a subinterval under a C¹ curve
    is bounded by the integral of the derivative norm.

    For s ≤ t ∈ [a,b] and γ differentiable on (a,b) with continuous
    derivative norm on [a,b]:
    ediam(γ '' Icc s t) ≤ ENNReal.ofReal(∫ u in s..t, ‖deriv γ u‖)

    Proof: For any p, q ∈ Icc s t:
    ‖γ(p) - γ(q)‖ = ‖∫ u in q..p, deriv γ u‖ ≤ ∫ u in s..t, ‖deriv γ u‖
    by norm_integral_le_integral_norm and monotonicity of the integral.
    Taking sup over p, q gives the diameter bound.
-/
lemma ediam_curve_image_le_integral {a b s t : ℝ} (_hab : a ≤ b) (hst : s ≤ t)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ u ∈ Ioo a b, DifferentiableAt ℝ γ u)
    (hγ_deriv_cont : ContinuousOn (fun u => ‖deriv γ u‖) (Icc a b)) :
    Metric.ediam (γ '' Icc s t) ≤
      ENNReal.ofReal (∫ u in s..t, ‖deriv γ u‖) := by
  -- We need to show that for any $x, y \in [s, t]$, $\| \gamma(x) - \gamma(y) \| \leq \int_s^t \| \gamma'(u) \| \, du$.
  have h_dist_le_integral : ∀ x y : ℝ, s ≤ x → x ≤ y → y ≤ t → ‖γ y - γ x‖ ≤ ∫ u in x..y, ‖deriv γ u‖ := by
    intros x y hx hy ht
    have h_ftc : γ y - γ x = ∫ u in x..y, deriv γ u := by
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy ];
      · exact hγ_cont.mono ( Set.Icc_subset_Icc ( by linarith [ hs.1 ] ) ( by linarith [ ‹t ∈ Icc a b›.2 ] ) );
      · exact fun u hu => DifferentiableAt.hasDerivAt ( hγ_diff u ⟨ by linarith [ hu.1, hs.1 ], by linarith [ hu.2, ht, ‹t ∈ Icc a b›.2 ] ⟩ );
      · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le hy ];
        have h_integrable : MeasureTheory.IntegrableOn (fun u => ‖deriv γ u‖) (Set.Ioo x y) := by
          exact hγ_deriv_cont.integrableOn_Icc.mono_set ( Set.Ioo_subset_Icc_self.trans ( Set.Icc_subset_Icc ( by linarith [ hs.1 ] ) ( by linarith [ ht, ‹t ∈ Icc a b›.2 ] ) ) );
        refine h_integrable.mono' ?_ ?_;
        · fun_prop;
        · exact Filter.Eventually.of_forall fun u => le_rfl
    rw [h_ftc];
    apply_rules [ intervalIntegral.norm_integral_le_integral_norm ];
  -- Since $γ$ is continuous on $[s, t]$, the image $γ '' [s, t]$ is also connected.
  have h_connected : ∀ x y : ℝ, s ≤ x → x ≤ y → y ≤ t → dist (γ y) (γ x) ≤ ∫ u in s..t, ‖deriv γ u‖ := by
    intro x y hx hy ht; rw [ dist_eq_norm ] ; refine le_trans ( h_dist_le_integral x y hx hy ht ) ?_;
    apply_rules [ intervalIntegral.integral_mono_interval ];
    · exact Filter.Eventually.of_forall fun u => norm_nonneg _;
    · apply_rules [ ContinuousOn.intervalIntegrable, hγ_deriv_cont ];
      exact hγ_deriv_cont.mono ( by rw [ uIcc_of_le hst ] ; exact Set.Icc_subset_Icc hs.1 ( by linarith [ Set.mem_Icc.mp ‹t ∈ Icc a b› ] ) );
  refine Metric.ediam_le ?_;
  rintro _ ⟨ x, hx, rfl ⟩ _ ⟨ y, hy, rfl ⟩ ; cases le_total x y <;> simp_all +decide [ edist_dist ];
  · simpa only [ dist_comm ] using ENNReal.ofReal_le_ofReal ( h_connected x y hx.1 ‹_› hy.2 );
  · exact ENNReal.ofReal_le_ofReal ( h_connected _ _ hy.1 ‹_› hx.2 )

/-! ## Lower bound ingredient 1: ∫ ‖γ'‖ ≤ eVariationOn -/

/-
For a C¹ curve γ on [a,b], the integral of the derivative norm
    is at most the total variation (eVariationOn).

    Proof: For any ε > 0, by uniform continuity of γ' on [a,b],
    for a fine enough partition tₖ:
    ‖γ(tₖ₊₁) - γ(tₖ)‖ = ‖∫_{tₖ}^{tₖ₊₁} γ'‖ ≥ ‖γ'(tₖ)‖·Δt - ε·Δt.
    Summing and taking sup gives eVariationOn ≥ ∫ ‖γ'‖.

Key estimate: for a differentiable curve γ, if the derivative is approximately
    constant (within ε) on a small interval, then the displacement is close to
    the derivative norm times the interval length.

    Specifically: ‖γ(t) - γ(s)‖ ≥ (‖γ'(s)‖ - ε) · (t - s) when γ' is within ε of γ'(s)
    on [s,t].
-/
lemma norm_sub_ge_of_deriv_approx {s t : ℝ} (hst : s ≤ t)
    {γ : ℝ → ℂ} {ε : ℝ} (_hε : ε ≥ 0)
    (hγ_cont : ContinuousOn γ (Icc s t))
    (hγ_diff : ∀ u ∈ Ioo s t, HasDerivAt γ (deriv γ u) u)
    (hγ_deriv_bound : ∀ u ∈ Icc s t, ‖deriv γ u - deriv γ s‖ ≤ ε)
    (hγ_intble : IntervalIntegrable (deriv γ) MeasureTheory.volume s t) :
    ‖γ t - γ s‖ ≥ (‖deriv γ s‖ - ε) * (t - s) := by
  -- By the fundamental theorem of calculus, we have γ(t) - γ(s) = ∫ u in s..t, deriv γ u.
  have h_ftc : γ t - γ s = ∫ u in s..t, deriv γ u := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
    · rwa [ Set.uIcc_of_le hst ];
    · exact fun x hx => HasDerivAt.hasDerivWithinAt ( hγ_diff x ⟨ by cases max_cases s t <;> cases min_cases s t <;> linarith [ hx.1, hx.2 ], by cases max_cases s t <;> cases min_cases s t <;> linarith [ hx.1, hx.2 ] ⟩ );
    · exact hγ_intble;
  -- Write deriv γ u = deriv γ s + (deriv γ u - deriv γ s). Then:
  have h_deriv_split : ∫ u in s..t, deriv γ u = (t - s) • deriv γ s + ∫ u in s..t, (deriv γ u - deriv γ s) := by
    rw [ intervalIntegral.integral_sub ];
    · rw [ intervalIntegral.integral_const ];
      rw [ add_comm ];
      exact ( sub_add_cancel _ _ ).symm;
    · exact hγ_intble;
    · exact intervalIntegrable_const;
  -- By the reverse triangle inequality:
  have h_reverse_triangle : ‖γ t - γ s‖ ≥ ‖(t - s) • deriv γ s‖ - ‖∫ u in s..t, (deriv γ u - deriv γ s)‖ := by
    simpa [ h_ftc, h_deriv_split, add_comm, add_left_comm, add_assoc ] using
      norm_sub_le ((t - s) • deriv γ s + ∫ u in s..t, (deriv γ u - deriv γ s))
        (∫ u in s..t, (deriv γ u - deriv γ s));
  -- For the error term:
  have h_error_term : ‖∫ u in s..t, (deriv γ u - deriv γ s)‖ ≤ ∫ u in s..t, ε := by
    rw [ intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst ];
    refine le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_ );
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
    · norm_num;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using hγ_deriv_bound u <| Set.Ioc_subset_Icc_self hu;
  norm_num at *;
  have hnorm : ‖((t : ℂ) - (s : ℂ))‖ = t - s := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hst)];
  have h_reverse_triangle' :
      (t - s) * ‖deriv γ s‖ ≤ ‖γ t - γ s‖ +
        ‖∫ u in s..t, (deriv γ u - deriv γ s)‖ := by
    simpa [hnorm] using h_reverse_triangle;
  nlinarith [h_reverse_triangle', h_error_term]

set_option maxHeartbeats 800000 in
-- This Riemann-sum proof is expensive because it combines partition estimates
-- with integral and variation bounds.
lemma integral_le_eVariationOn {a b : ℝ} (hab : a < b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤
      eVariationOn γ (Icc a b) := by
  have h_riemann_sum : ∀ ε > 0, ∃ N : ℕ, N ≠ 0 ∧ ∑ k ∈ Finset.range N, ‖γ (a + (k + 1) * (b - a) / N) - γ (a + k * (b - a) / N)‖ ≥ (∫ t in a..b, ‖deriv γ t‖) - ε := by
    intro ε hε_pos
    obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ u ∈ Set.Icc a b, |t - u| < δ → ‖deriv γ t - deriv γ u‖ < ε / (2 * (b - a)) := by
      obtain ⟨δ, δ_pos, hδ⟩ :=
        Metric.uniformContinuousOn_iff.mp
          (isCompact_Icc.uniformContinuousOn_of_continuous hγ_deriv_cont)
          (ε / (2 * (b - a)))
          (div_pos hε_pos (mul_pos zero_lt_two (sub_pos.mpr hab)));
      refine ⟨δ, δ_pos, ?_⟩;
      intro t ht u hu htu;
      have hdist : dist t u < δ := by simpa [Real.dist_eq] using htu;
      simpa [Complex.dist_eq] using hδ t ht u hu hdist;
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N ≠ 0 ∧ (b - a) / N < δ := by
      exact ⟨ ⌊ ( b - a ) / δ⌋₊ + 1, Nat.succ_ne_zero _, by rw [ div_lt_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( ( b - a ) / δ ), mul_div_cancel₀ ( b - a ) δ_pos.ne' ] ⟩;
    -- By the properties of the integral, we can approximate the integral of the derivative norm by the sum of the norms of the differences of γ over the partition.
    have h_integral_approx : |∑ k ∈ Finset.range N, ‖deriv γ (a + k * (b - a) / N)‖ * (b - a) / N - ∫ t in a..b, ‖deriv γ t‖| ≤ ε / 2 := by
      have h_integral_approx : |∑ k ∈ Finset.range N, ∫ t in (a + k * (b - a) / N).. (a + (k + 1) * (b - a) / N), ‖deriv γ t‖ - ‖deriv γ (a + k * (b - a) / N)‖| ≤ ε / 2 := by
        have h_integral_approx : ∀ k ∈ Finset.range N, |∫ t in (a + k * (b - a) / N).. (a + (k + 1) * (b - a) / N), ‖deriv γ t‖ - ‖deriv γ (a + k * (b - a) / N)‖| ≤ (ε / (2 * (b - a))) * ((b - a) / N) := by
          intros k hk
          have h_integral_approx : ∀ t ∈ Set.Icc (a + k * (b - a) / N) (a + (k + 1) * (b - a) / N), |‖deriv γ t‖ - ‖deriv γ (a + k * (b - a) / N)‖| ≤ ε / (2 * (b - a)) := by
            intros t ht
            have h_dist : |t - (a + k * (b - a) / N)| < δ := by
              grind +splitImp;
            have := hδ t ⟨ by nlinarith [ ht.1, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ], by nlinarith [ ht.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k + 1 : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ⟩ ( a + k * ( b - a ) / N ) ⟨ by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ], by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ⟩ h_dist;
            exact le_trans ( abs_norm_sub_norm_le _ _ ) this.le;
          refine le_trans ( intervalIntegral.abs_integral_le_integral_abs ?_ ) ?_;
          · bound;
          · refine le_trans ( intervalIntegral.integral_mono_on ?_ ?_ ?_ h_integral_approx ) ?_ <;> norm_num;
            · bound;
            · apply_rules [ ContinuousOn.intervalIntegrable ];
              exact ContinuousOn.abs ( ContinuousOn.sub ( ContinuousOn.norm ( hγ_deriv_cont.mono ( by rw [ uIcc_of_le ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), div_mul_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) ] ; exact fun x hx => ⟨ by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), div_mul_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), hx.1, hx.2 ], by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], div_mul_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), div_mul_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), hx.1, hx.2 ] ⟩ ) ) ) continuousOn_const );
            · ring_nf; norm_num;
        refine le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( le_trans ( Finset.sum_le_sum h_integral_approx ) ?_ );
        norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hN.1 ];
        norm_num [ ne_of_gt ( sub_pos.mpr hab ) ];
      convert h_integral_approx using 1;
      rw [ Finset.sum_congr rfl fun i hi => intervalIntegral.integral_sub ?_ ?_ ] <;> norm_num;
      · rw [ show ( ∫ t in a..b, ‖deriv γ t‖ ) = ∑ k ∈ Finset.range N, ∫ t in ( a + k * ( b - a ) / N ).. ( a + ( k + 1 ) * ( b - a ) / N ), ‖deriv γ t‖ from ?_ ];
        · rw [ abs_sub_comm ] ; congr ; ext ; ring;
        · symm;
          convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num [ hN.1 ];
          intro k hk; apply_rules [ ContinuousOn.intervalIntegrable ];
          exact ContinuousOn.norm ( hγ_deriv_cont.mono ( by rw [ uIcc_of_le ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast, mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ) ] ) ] ; exact fun x hx => ⟨ by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast, mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), hx.1, hx.2 ], by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast, mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( by norm_cast; linarith : ( N : ℝ ) ≠ 0 ), hx.1, hx.2 ] ⟩ ) );
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact ContinuousOn.norm ( hγ_deriv_cont.mono ( by rw [ uIcc_of_le ( by nlinarith [ show ( i : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hi ], mul_div_cancel₀ ( ( i : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( i : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) ] ; exact fun x hx => ⟨ by nlinarith [ show ( i : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hi ], mul_div_cancel₀ ( ( i : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( i : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), hx.1, hx.2 ], by nlinarith [ show ( i : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hi ], mul_div_cancel₀ ( ( i : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( i : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), hx.1, hx.2 ] ⟩ ) );
    have h_sum_approx : ∀ k ∈ Finset.range N, ‖γ (a + (k + 1) * (b - a) / N) - γ (a + k * (b - a) / N)‖ ≥ ‖deriv γ (a + k * (b - a) / N)‖ * (b - a) / N - ε / (2 * N) := by
      intro k hk
      have h_approx : ‖γ (a + (k + 1) * (b - a) / N) - γ (a + k * (b - a) / N)‖ ≥ ‖deriv γ (a + k * (b - a) / N)‖ * (b - a) / N - ε / (2 * N) := by
        have h_deriv_approx : ∀ u ∈ Set.Icc (a + k * (b - a) / N) (a + (k + 1) * (b - a) / N), ‖deriv γ u - deriv γ (a + k * (b - a) / N)‖ ≤ ε / (2 * (b - a)) := by
          intros u hu
          have h_diff : |u - (a + k * (b - a) / N)| < δ := by
            exact abs_lt.mpr ⟨ by nlinarith [ hu.1, hu.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), div_mul_cancel₀ ( b - a ) ( Nat.cast_ne_zero.mpr hN.1 ) ], by nlinarith [ hu.1, hu.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), div_mul_cancel₀ ( b - a ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ⟩;
          exact le_of_lt ( hδ u ⟨ by nlinarith [ hu.1, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( show ( N : ℝ ) ≠ 0 by norm_cast; linarith [ Finset.mem_range.mp hk ] ) ], by nlinarith [ hu.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k + 1 : ℝ ) * ( b - a ) ) ( show ( N : ℝ ) ≠ 0 by norm_cast; linarith [ Finset.mem_range.mp hk ] ) ] ⟩ ( a + k * ( b - a ) / N ) ⟨ by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( show ( N : ℝ ) ≠ 0 by norm_cast; linarith [ Finset.mem_range.mp hk ] ) ], by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( show ( N : ℝ ) ≠ 0 by norm_cast; linarith [ Finset.mem_range.mp hk ] ) ] ⟩ h_diff )
        have := @norm_sub_ge_of_deriv_approx ( a + k * ( b - a ) / N ) ( a + ( k + 1 ) * ( b - a ) / N ) ?_ ?_ ?_ ?_ ?_ ?_;
        rotate_left;
        any_goals exact γ;
        any_goals exact ε / ( 2 * ( b - a ) );
        · bound;
        · exact div_nonneg hε_pos.le ( mul_nonneg zero_le_two ( sub_nonneg.mpr hab.le ) );
        · exact hγ_cont.mono ( Set.Icc_subset_Icc ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k + 1 : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) );
        · exact fun u hu => DifferentiableAt.hasDerivAt ( hγ_diff u ⟨ by nlinarith [ hu.1, hu.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ], by nlinarith [ hu.1, hu.2, show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ⟩ );
        · convert this h_deriv_approx _ using 1;
          · grind +qlia;
          · apply_rules [ ContinuousOn.intervalIntegrable, hγ_deriv_cont ];
            exact hγ_deriv_cont.mono ( by rw [ uIcc_of_le ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) ] ; exact Set.Icc_subset_Icc ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) ( by nlinarith [ show ( k : ℝ ) + 1 ≤ N by norm_cast; linarith [ Finset.mem_range.mp hk ], mul_div_cancel₀ ( ( k : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ), mul_div_cancel₀ ( ( ( k : ℝ ) + 1 ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN.1 ) ] ) );
      exact h_approx;
    refine ⟨ N, hN.1, ?_ ⟩;
    refine le_trans ?_ ( Finset.sum_le_sum h_sum_approx );
    norm_num [ div_eq_mul_inv, Finset.sum_mul _ _ _ ] at *;
    nlinarith [ abs_le.mp h_integral_approx, mul_inv_cancel_left₀ ( Nat.cast_ne_zero.mpr hN.1 ) ε ];
  have h_eVariationOn_ge_Riemann_sum : ∀ N : ℕ, N ≠ 0 → eVariationOn γ (Icc a b) ≥ ENNReal.ofReal (∑ k ∈ Finset.range N, ‖γ (a + (k + 1) * (b - a) / N) - γ (a + k * (b - a) / N)‖) := by
    intro N hN_nonzero
    have h_partition : ∃ p : Fin (N + 1) → ℝ, Monotone p ∧ ∀ i : Fin (N + 1), p i ∈ Set.Icc a b ∧ p i = a + i * (b - a) / N := by
      refine ⟨ fun i => a + i * ( b - a ) / N, ?_, ?_ ⟩ <;> norm_num [ Monotone ];
      · field_simp;
        exact fun i j hij => by rw [ mul_comm ] ; exact mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr hij ) ( sub_nonneg.mpr hab.le ) ;
      · exact fun i => ⟨ div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr hab.le ) ) ( Nat.cast_nonneg _ ), by nlinarith [ show ( i : ℝ ) ≤ N by norm_cast; linarith [ Fin.is_le i ], show ( N : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hN_nonzero ), mul_div_cancel₀ ( ( i : ℝ ) * ( b - a ) ) ( Nat.cast_ne_zero.mpr hN_nonzero ) ] ⟩;
    obtain ⟨ p, hp₁, hp₂ ⟩ := h_partition; simp_all +decide [ Finset.sum_range, Fin.sum_univ_castSucc ] ;
    refine le_csSup ?_ ?_;
    · exact ⟨ ⊤, fun _ _ => le_top ⟩
    · norm_num [ hp₂ ];
      refine ⟨ N, fun i => if hi : i < N + 1 then p ⟨ i, hi ⟩ else b, ?_, ?_ ⟩ <;> simp_all +decide [ Monotone ];
      · constructor <;> intro i <;> split_ifs <;> norm_num [ hp₂ ];
        · intro j hj; split_ifs <;> simp_all +decide  ;
          · exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr hj ) ( sub_nonneg.mpr hab.le ) ) ( Nat.cast_nonneg _ );
          · exact hp₂ ⟨ i, by linarith ⟩ |>.2 ▸ hp₂ ⟨ i, by linarith ⟩ |>.1 |>.2;
        · intro j hj; split_ifs <;> linarith;
        · exact ⟨ div_nonneg ( mul_nonneg ( Nat.cast_nonneg _ ) ( sub_nonneg.mpr hab.le ) ) ( Nat.cast_nonneg _ ), by rw [ add_div', div_le_iff₀ ] <;> nlinarith [ show ( i : ℝ ) ≤ N by norm_cast, show ( N : ℝ ) > 0 by positivity ] ⟩;
        · linarith;
      · rw [ ENNReal.ofReal_sum_of_nonneg ] <;> norm_num [ edist_dist ];
        rw [ Finset.sum_range ] ; congr ; ext i ; simp +decide [ dist_eq_norm ] ;
  have h_eVariationOn_ge_integral : ∀ ε > 0, eVariationOn γ (Icc a b) ≥ ENNReal.ofReal ((∫ t in a..b, ‖deriv γ t‖) - ε) := by
    exact fun ε hε => by obtain ⟨ N, hN₁, hN₂ ⟩ := h_riemann_sum ε hε; exact le_trans ( ENNReal.ofReal_le_ofReal hN₂ ) ( h_eVariationOn_ge_Riemann_sum N hN₁ ) ;
  have h_eVariationOn_ge_integral : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal ((∫ t in a..b, ‖deriv γ t‖) - ε)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖))) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using ENNReal.tendsto_ofReal ( Continuous.tendsto ( show Continuous fun ε : ℝ => ( ∫ t in a..b, ‖deriv γ t‖ ) - ε from continuous_const.sub continuous_id' ) 0 ) );
  exact le_of_tendsto h_eVariationOn_ge_integral ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop )

/-! ## Lower bound ingredient 2: eVariationOn ≤ μH[1](image) for injective curves -/

/-
For a continuous curve γ on [a,b] that is injective on (a,b),
    the total variation is at most the Hausdorff 1-measure of the image.

    Proof: For any partition a = t₀ < t₁ < ... < tₙ = b:
    1. edist(γ(tₖ), γ(tₖ₊₁)) ≤ μH[1](γ '' Icc tₖ tₖ₊₁)
       (by hausdorffMeasure_connected_ge_edist, since the image is connected)
    2. μH[1](γ '' Icc tₖ tₖ₊₁) = μH[1](γ '' Ioo tₖ tₖ₊₁)
       (since the difference is a finite set with μH[1] = 0)
    3. γ '' Ioo tₖ tₖ₊₁ are pairwise disjoint (by injectivity on (a,b))
    4. γ '' Ioo tₖ tₖ₊₁ are Borel measurable
       (by MeasurableSet.image_of_continuousOn_injOn, since ℝ is Polish)
    5. Σ μH[1](γ '' Ioo tₖ tₖ₊₁) = μH[1](∪ γ '' Ioo tₖ tₖ₊₁) ≤ μH[1](γ '' Icc a b)
       (by measure_iUnion for disjoint measurable sets + monotonicity)
    Taking sup over partitions: eVariationOn ≤ μH[1](image).
-/
lemma eVariationOn_le_hausdorffMeasure_injective {a b : ℝ} (_hab : a < b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_inj : InjOn γ (Ioo a b)) :
    eVariationOn γ (Icc a b) ≤
      μH[(1 : ℝ)] (γ '' Icc a b) := by
  refine iSup_le ?_;
  intro ⟨ n, ⟨ u, hu ⟩ ⟩;
  -- Claim 1: edist(γ(u i), γ(u(i+1))) ≤ μH[1](sᵢ).
  have h_edist_le_measure (i : ℕ) (hi : i < n) : edist (γ (u (i + 1))) (γ (u i)) ≤ μH[1] (γ '' Set.Ioo (u i) (u (i + 1))) := by
    by_cases h_cases : u (i + 1) = u i;
    · aesop;
    · have h_edist_le_measure : edist (γ (u (i + 1))) (γ (u i)) ≤ μH[1] (γ '' Set.Icc (u i) (u (i + 1))) := by
        apply_rules [ hausdorffMeasure_connected_ge_edist ];
        · exact isPreconnected_Icc.image _ ( hγ_cont.mono ( Set.Icc_subset_Icc ( hu.2 i |>.1 ) ( hu.2 ( i + 1 ) |>.2 ) ) );
        · exact ⟨ u ( i + 1 ), ⟨ by linarith [ hu.1 ( Nat.le_succ i ) ], by linarith [ hu.1 ( Nat.le_succ i ) ] ⟩, rfl ⟩;
        · exact ⟨ u i, ⟨ le_rfl, hu.1 ( Nat.le_succ _ ) ⟩, rfl ⟩;
      have h_eq_measure : μH[1] (γ '' Set.Icc (u i) (u (i + 1))) = μH[1] (γ '' Set.Ioo (u i) (u (i + 1))) := by
        have h_diff : γ '' Set.Icc (u i) (u (i + 1)) = γ '' Set.Ioo (u i) (u (i + 1)) ∪ {γ (u i), γ (u (i + 1))} := by
          ext x;
          constructor;
          · rintro ⟨ y, hy, rfl ⟩ ; cases eq_or_lt_of_le hy.1 <;> cases eq_or_lt_of_le hy.2 <;> aesop;
          · rintro ( ⟨ y, hy, rfl ⟩ | rfl | rfl ) <;> [ exact ⟨ y, ⟨ hy.1.le, hy.2.le ⟩, rfl ⟩ ; exact ⟨ u i, ⟨ le_rfl, hu.1 ( Nat.le_succ _ ) ⟩, rfl ⟩ ; exact ⟨ u ( i + 1 ), ⟨ hu.1 ( Nat.le_succ _ ), le_rfl ⟩, rfl ⟩ ]
        rw [ h_diff, MeasureTheory.measure_union₀ ] <;> norm_num;
        · rw [ Set.insert_eq, MeasureTheory.measure_union_null ] <;> norm_num;
          · simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ];
            intro ε hε; refine le_antisymm ?_ ?_;
            · refine le_trans ( ciInf_le ?_ ( fun _ => { γ ( u i ) } ) ) ?_ <;> norm_num;
            · exact zero_le _;
          · simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ];
            intro ε hε; refine le_antisymm ?_ ?_;
            · refine le_trans ( ciInf_le ?_ ( fun _ => { γ ( u ( i + 1 ) ) } ) ) ?_ <;> norm_num;
            · exact zero_le _;
        · refine MeasureTheory.measure_mono_null
            (t := { γ ( u i ), γ ( u ( i + 1 ) ) }) ?_ ?_;
          · exact Set.inter_subset_right;
          · rw [ Set.insert_eq, MeasureTheory.measure_union_null ];
            · simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ];
              intro ε hε; refine le_antisymm ?_ ?_;
              · refine le_trans ( ciInf_le ?_ ( fun _ => { γ ( u i ) } ) ) ?_ <;> norm_num;
              · exact zero_le _;
            · simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ];
              intro ε hε; refine le_antisymm ?_ ?_;
              · refine le_trans ( ciInf_le ?_ ( fun _ => { γ ( u ( i + 1 ) ) } ) ) ?_ <;> norm_num;
              · exact zero_le _;
      exact h_eq_measure ▸ h_edist_le_measure;
  refine le_trans ( Finset.sum_le_sum fun i hi => h_edist_le_measure i ( Finset.mem_range.mp hi ) ) ?_;
  rw [ ← MeasureTheory.measure_biUnion_finset ];
  · refine MeasureTheory.measure_mono ?_;
    simp +decide [ Set.subset_def ];
    exact fun x i hi y hy₁ hy₂ hx => ⟨ y, ⟨ by linarith [ hu.2 i |>.1 ], by linarith [ hu.2 ( i + 1 ) |>.2 ] ⟩, hx ⟩;
  · intros i hi j hj hij;
    cases lt_or_gt_of_ne hij <;> simp_all +decide [ Set.disjoint_left ];
    · intro a x hx₁ hx₂ hx₃ y hy₁ hy₂ hy₃; have := hu.1 ( show i + 1 ≤ j from by linarith ) ; simp_all +decide  ;
      exact absurd ( hγ_inj ( show x ∈ Set.Ioo _ _ from ⟨ by linarith [ hu.2 i ], by linarith [ hu.2 ( i + 1 ), hu.2 j, hu.2 ( j + 1 ) ] ⟩ ) ( show y ∈ Set.Ioo _ _ from ⟨ by linarith [ hu.2 i, hu.2 ( i + 1 ), hu.2 j, hu.2 ( j + 1 ) ], by linarith [ hu.2 i, hu.2 ( i + 1 ), hu.2 j, hu.2 ( j + 1 ) ] ⟩ ) <| by aesop ) ( by linarith );
    · rintro _ x hx₁ hx₂ rfl y hy₁ hy₂;
      exact fun h => absurd ( hγ_inj ( show y ∈ Set.Ioo a b from ⟨ by linarith [ hu.2 j |>.1, hu.2 j |>.2 ], by linarith [ hu.2 ( j + 1 ) |>.1, hu.2 ( j + 1 ) |>.2, hu.1 ( show j + 1 ≤ i from by linarith ) ] ⟩ ) ( show x ∈ Set.Ioo a b from ⟨ by linarith [ hu.2 i |>.1, hu.2 i |>.2, hu.1 ( show i ≤ i + 1 from by linarith ) ], by linarith [ hu.2 ( i + 1 ) |>.1, hu.2 ( i + 1 ) |>.2 ] ⟩ ) h ) ( by linarith [ hu.1 ( show j + 1 ≤ i from by linarith ) ] );
  · intro i hi
    have h_image_measurable : MeasurableSet (γ '' Set.Ioo (u i) (u (i + 1))) := by
      have h_cont : ContinuousOn γ (Set.Icc (u i) (u (i + 1))) := by
        exact hγ_cont.mono ( Set.Icc_subset_Icc ( hu.2 i |>.1 ) ( hu.2 ( i + 1 ) |>.2 ) )
      have h_inj : InjOn γ (Set.Ioo (u i) (u (i + 1))) := by
        exact hγ_inj.mono ( Set.Ioo_subset_Ioo ( hu.2 i |>.1 ) ( hu.2 ( i + 1 ) |>.2 ) )
      apply_rules [ MeasurableSet.image_of_continuousOn_injOn ];
      · exact measurableSet_Ioo;
      · exact h_cont.mono <| Set.Ioo_subset_Icc_self
    exact h_image_measurable

end Erdos1044


/-! ### From FrontierIdent.lean -/

/-
  Frontier identification sub-lemmas for the lemniscate petal.

  This file proves that the frontier of the connected component of
  OmegaSet(z^n - 1) containing 1 equals the image of the lemniscate
  petal curve. The proof decomposes into:

  A. The petal curve lies on the lemniscate (‖eval‖ = 1)
  B. The petal curve image ⊆ frontier (approach from inside + not in OmegaSet)
  C. The frontier ⊆ petal curve image (arg bound + lemniscate equation)
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Frontier of component lies on the lemniscate -/

/-
The frontier of any connected component of OmegaSet(f) is contained
    in the level set {z : ‖f.eval z‖ = 1}.
-/
lemma frontier_component_sub_lemniscate' (f : Polynomial ℂ) (z : ℂ)
    (_hz : z ∈ OmegaSet f) :
    frontier (connectedComponentIn (OmegaSet f) z) ⊆
      {w : ℂ | ‖f.eval w‖ = 1} := by
  intro w hw;
  by_cases hw_in : w ∈ OmegaSet f;
  · simp_all +decide [ frontier_eq_closure_inter_closure ];
    contrapose! hw;
    -- Since $w \in \Omega(f)$ and $\Omega(f)$ is open, $w$ is in the interior of its connected component.
    have h_interior : w ∈ connectedComponentIn (OmegaSet f) w := by
      exact mem_connectedComponentIn hw_in
    by_cases h : connectedComponentIn ( OmegaSet f ) w = connectedComponentIn ( OmegaSet f ) z <;> simp_all +decide ;
    · rw [ mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ];
      have h_open : IsOpen (connectedComponentIn (OmegaSet f) z) := by
        apply_rules [ IsOpen.connectedComponentIn, omegaSet_isOpen ];
      exact fun _ => Metric.mem_nhds_iff.mp ( h_open.mem_nhds h_interior );
    · intro hw_closure
      have h_disjoint : Disjoint (connectedComponentIn (OmegaSet f) w) (connectedComponentIn (OmegaSet f) z) := by
        rw [ Set.disjoint_left ];
        intro x hx hx'; have := connectedComponentIn_eq hx; have := connectedComponentIn_eq hx'; aesop;
      rw [ mem_closure_iff_nhds ] at hw_closure;
      specialize hw_closure ( connectedComponentIn ( OmegaSet f ) w ) ( IsOpen.mem_nhds ( show IsOpen ( connectedComponentIn ( OmegaSet f ) w ) from by
                                                                                            apply_rules [ IsOpen.connectedComponentIn, omegaSet_isOpen ] ) h_interior ) ; simp_all +decide [ Set.disjoint_left ];
      exact False.elim <| hw_closure.elim fun x hx => h_disjoint hx.1 hx.2;
  · -- Since $w$ is in the closure of the connected component of $\Omega(f)$ containing $z$, we have $w \in \overline{\Omega(f)}$.
    have hw_closure : w ∈ closure (OmegaSet f) := by
      exact closure_mono ( connectedComponentIn_subset _ _ ) hw.1;
    simp_all +decide [ OmegaSet, mem_closure_iff_seq_limit ];
    exact le_antisymm ( le_of_tendsto_of_tendsto' ( Filter.Tendsto.norm ( f.continuous.continuousAt.tendsto.comp hw_closure.choose_spec.2 ) ) tendsto_const_nhds fun n => le_of_lt ( hw_closure.choose_spec.1 n ) ) hw_in

/-! ## Helper: the disk B(1,1) is contained in {Re > 0} -/

/-- The open ball B(1,1) = {w : |w-1| < 1} in ℂ is contained in {w : 0 < w.re}. -/
lemma ball_one_one_sub_re_pos : Metric.ball (1 : ℂ) 1 ⊆ {w : ℂ | 0 < w.re} := by
  norm_num [ Set.subset_def, Complex.dist_eq ]
  norm_num [ Complex.normSq, Complex.norm_def ]
  exact fun x hx => by rw [ Real.sqrt_lt' ] at hx <;> nlinarith

/-! ## Sub-lemma: the petal curve lies on the lemniscate -/

/-- For θ ∈ Icc, the lemniscate petal curve satisfies ‖(modelPoly n).eval (γ(θ))‖ = 1. -/
lemma lemniscatePetalCurve_on_lemniscate (n : ℕ) (hn : n ≥ 1)
    (θ : ℝ) (hθ : θ ∈ Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n))) :
    ‖(modelPoly n).eval (lemniscatePetalCurve n θ)‖ = 1 := by
  unfold lemniscatePetalCurve modelPoly
  have h_cos_nonneg : 0 ≤ Real.cos (n * θ) := by
    exact Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.1, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.2, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩
  norm_num [ mul_pow, ← Complex.exp_nat_mul, h_cos_nonneg ]
  norm_cast ; norm_num [ ← Real.rpow_natCast, ← Real.rpow_mul ( mul_nonneg zero_le_two h_cos_nonneg ), show n ≠ 0 by linarith ]
  norm_num [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ]
  norm_cast; ring_nf; rw [ Real.sin_sq, Real.cos_sq ] ; ring_nf
  rw [ show ( n : ℝ ) * θ * 2 = 2 * ( n * θ ) by ring, Real.cos_two_mul ] ; nlinarith [ Real.cos_sq' ( n * θ ) ]

/-! ## Sub-lemma: scaled petal points are in OmegaSet -/

/-- For 0 < ε < 1 and θ ∈ (-π/(2n), π/(2n)), the scaled petal point is in OmegaSet. -/
lemma scaled_petal_in_omegaSet (n : ℕ) (hn : n ≥ 1)
    (θ : ℝ) (hθ : θ ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)))
    (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1) :
    (((1 - ε) * (2 * Real.cos (↑n * θ))) ^ ((1 : ℝ) / ↑n) : ℝ) *
      Complex.exp (↑θ * Complex.I) ∈ OmegaSet (modelPoly n) := by
  set c := (1 - ε) * (2 * Real.cos (n * θ))
  set r := c ^ (1 / n : ℝ)
  have hz : (((r : ℂ) * cexp (θ * Complex.I)) ^ n - 1) = (c * Complex.exp (n * θ * Complex.I)) - 1 := by
    rw [ mul_pow, ← Complex.exp_nat_mul ] ; ring_nf
    rw [ mul_comm, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul ] <;> norm_num [ show n ≠ 0 by linarith ]
    exact mul_nonneg ( by linarith ) ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.1, hθ.2, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.1, hθ.2, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ) )
  have h_abs : ‖((c : ℂ) * Complex.exp (n * θ * Complex.I)) - 1‖ ^ 2 < 1 := by
    rw [ ← Complex.normSq_eq_norm_sq, Complex.normSq_sub ] ; norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf
    rw [ Real.sin_sq ] ; ring_nf
    nlinarith [ show 0 < Real.cos ( n * θ ) ^ 2 by exact sq_pos_of_pos ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.2 ] ⟩ ), mul_pos hε₁ ( sub_pos.mpr hε₂ ) ]
  simp_all +decide [ OmegaSet, modelPoly ]

/-! ## Sub-lemma: scaled petal connected to 1 -/

/-- Scaled petal points are in the connected component containing 1. -/
lemma petal_curve_connected_to_one (n : ℕ) (hn : n ≥ 1)
    (θ : ℝ) (hθ : θ ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)))
    (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1) :
    (((1 - ε) * (2 * Real.cos (↑n * θ))) ^ ((1 : ℝ) / ↑n) : ℝ) *
      Complex.exp (↑θ * Complex.I) ∈
      connectedComponentIn (OmegaSet (modelPoly n)) 1 := by
  have h_real_axis_path : ∃ γ : ℝ → ℂ, Continuous γ ∧ γ 0 = 1 ∧ γ 1 = (((1 - ε) * (2 * Real.cos (n * θ))) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I) ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ OmegaSet (modelPoly n) := by
    have h_real_axis_path : ∃ γ : ℝ → ℂ, Continuous γ ∧ γ 0 = (((1 - ε) * 2) ^ ((1 : ℝ) / n) : ℝ) ∧ γ 1 = (((1 - ε) * (2 * Real.cos (n * θ))) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I) ∧ ∀ t ∈ Set.Icc 0 1, γ t ∈ OmegaSet (modelPoly n) := by
      refine ⟨ fun t => ( ( ( 1 - ε ) * ( 2 * Real.cos ( n * ( t * θ ) ) ) ) ^ ( ( 1 : ℝ ) / n ) : ℝ ) * Complex.exp ( t * θ * Complex.I ), ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ Complex.exp_ne_zero ]
      · exact Continuous.mul ( Complex.continuous_ofReal.comp <| Continuous.rpow_const ( by continuity ) <| by continuity ) <| Complex.continuous_exp.comp <| by continuity
      · intro t ht₁ ht₂; convert scaled_petal_in_omegaSet n hn ( t * θ ) ⟨ by nlinarith [ hθ.1, hθ.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ hθ.1, hθ.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ε hε₁ hε₂ using 1; ring_nf
        norm_num [ mul_assoc, mul_comm, mul_left_comm ]
    obtain ⟨γ, hγ_cont, hγ₀, hγ₁, hγ⟩ := h_real_axis_path
    have h_real_axis_path : ∃ γ' : ℝ → ℂ, Continuous γ' ∧ γ' 0 = 1 ∧ γ' 1 = (((1 - ε) * 2) ^ ((1 : ℝ) / n) : ℝ) ∧ ∀ t ∈ Set.Icc 0 1, γ' t ∈ OmegaSet (modelPoly n) := by
      refine ⟨ fun t => ( 1 - t ) + t * ( ( ( 1 - ε ) * 2 ) ^ ( 1 / ( n : ℝ ) ) : ℝ ), ?_, ?_, ?_, ?_ ⟩ <;> norm_num
      · fun_prop
      · intro t ht₁ ht₂; unfold OmegaSet; norm_num [ modelPoly ]
        have h_bound : 0 < ((1 - ε) * 2) ^ (1 / n : ℝ) ∧ ((1 - ε) * 2) ^ (1 / n : ℝ) < 2 ^ (1 / n : ℝ) := by
          exact ⟨ Real.rpow_pos_of_pos ( by linarith ) _, Real.rpow_lt_rpow ( by linarith ) ( by linarith ) ( by positivity ) ⟩
        have h_bound : 0 < (1 - t) + t * ((1 - ε) * 2) ^ (1 / n : ℝ) ∧ (1 - t) + t * ((1 - ε) * 2) ^ (1 / n : ℝ) < 2 ^ (1 / n : ℝ) := by
          constructor <;> cases lt_or_eq_of_le ht₁ <;> cases lt_or_eq_of_le ht₂ <;> nlinarith [ show ( 2 : ℝ ) ^ ( 1 / ( n : ℝ ) ) > 1 by exact Real.one_lt_rpow ( by norm_num ) ( by positivity ) ]
        have h_abs : |(1 - t) + t * ((1 - ε) * 2) ^ (1 / n : ℝ)| ^ n < 2 := by
          rw [ abs_of_pos h_bound.1 ] ; exact lt_of_lt_of_le ( pow_lt_pow_left₀ h_bound.2 ( by linarith ) ( by linarith ) ) ( by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] )
        norm_cast ; norm_num at *
        rw [ abs_lt ]
        constructor <;> linarith [ pow_pos h_bound.1 n, abs_of_pos h_bound.1, pow_le_pow_left₀ ( by linarith ) ( show |1 - t + t * ( ( 1 - ε ) * 2 ) ^ ( n : ℝ ) ⁻¹| ≥ 1 - t + t * ( ( 1 - ε ) * 2 ) ^ ( n : ℝ ) ⁻¹ by rw [ abs_of_pos h_bound.1 ] ) n ]
    obtain ⟨γ', hγ'_cont, hγ'_0, hγ'_1, hγ'⟩ := h_real_axis_path
    use fun t => if t ≤ 1 / 2 then γ' (2 * t) else γ (2 * t - 1)
    refine ⟨ ?_, ?_, ?_, ?_ ⟩ <;> norm_num [ hγ'_0, hγ'_1, hγ₀, hγ₁ ]
    · apply_rules [ Continuous.if_le, Continuous.sub, Continuous.mul, continuous_id, continuous_const ] <;> norm_num
      · exact hγ'_cont.comp ( continuous_const.mul continuous_id' )
      · exact hγ_cont.comp <| Continuous.sub ( continuous_const.mul continuous_id' ) continuous_const
      · aesop
    · intro t ht₁ ht₂; split_ifs <;> [ exact hγ' _ ⟨ by linarith, by linarith ⟩ ; exact hγ _ ⟨ by linarith, by linarith ⟩ ]
  obtain ⟨ γ, hγ₁, hγ₂, hγ₃, hγ₄ ⟩ := h_real_axis_path
  have h_image : Set.image γ (Set.Icc 0 1) ⊆ connectedComponentIn (OmegaSet (modelPoly n)) 1 := by
    apply_rules [ IsPreconnected.subset_connectedComponentIn ]
    · exact isPreconnected_Icc.image _ hγ₁.continuousOn
    · exact ⟨ 0, by norm_num, hγ₂ ⟩
    · exact Set.image_subset_iff.mpr hγ₄
  exact hγ₃ ▸ h_image ⟨ 1, by norm_num, rfl ⟩

/-! ## Sub-lemma: petal curve ⊆ closure of component -/

/-- The lemniscate petal curve image is contained in the closure of the component. -/
lemma petal_curve_sub_closure (n : ℕ) (hn : n ≥ 1) :
    lemniscatePetalCurve n '' Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) ⊆
      closure (connectedComponentIn (OmegaSet (modelPoly n)) 1) := by
  have h_seq : ∀ θ ∈ Icc (-(Real.pi / (2 * n))) (Real.pi / (2 * n)), ∃ seq : ℕ → ℂ, (∀ k, seq k ∈ connectedComponentIn (OmegaSet (modelPoly n)) 1) ∧ Filter.Tendsto seq Filter.atTop (nhds (lemniscatePetalCurve n θ)) := by
    intro θ hθ
    by_cases hθ' : θ = - ( Real.pi / ( 2 * n ) ) ∨ θ = Real.pi / ( 2 * n )
    · obtain ⟨seq, hseq⟩ : ∃ seq : ℕ → ℝ, (∀ k, seq k ∈ Set.Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n))) ∧ Filter.Tendsto seq Filter.atTop (nhds θ) := by
        rcases hθ' with hθ' | hθ'
        · refine ⟨ fun k => - ( Real.pi / ( 2 * n ) ) + ( Real.pi / ( 2 * n ) ) / ( k + 1 ), ?_, ?_ ⟩ <;> norm_num
          · exact fun k => ⟨ by positivity, lt_add_of_le_of_pos ( div_le_self ( by positivity ) ( by linarith ) ) ( by positivity ) ⟩
          · exact hθ'.symm ▸ le_trans ( tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) ( by norm_num )
        · use fun k => Real.pi / ( 2 * n ) - 1 / ( k + 1 ) * ( Real.pi / ( 2 * n ) )
          field_simp
          constructor
          · intro k; constructor <;> ring_nf <;> norm_num [ Real.pi_pos, show n ≠ 0 by linarith ]
            · exact neg_lt_iff_pos_add'.mpr ( by positivity )
            · field_simp; norm_num
          · convert tendsto_natCast_div_add_atTop ( 1 : ℝ ) |> Filter.Tendsto.const_mul ( Real.pi / ( 2 * n ) ) using 2 <;> ring_nf
            · field_simp; ring
            · exact hθ'.trans ( by ring )
      use fun k => (((1 - 1 / (k + 2)) * (2 * Real.cos (n * seq k))) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (seq k * Complex.I)
      constructor
      · intro k
        convert petal_curve_connected_to_one n hn ( seq k ) ( hseq.1 k ) ( 1 / ( k + 2 ) ) ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> linarith ) using 1
      · convert Filter.Tendsto.mul ( Complex.continuous_ofReal.continuousAt.tendsto.comp <| Filter.Tendsto.rpow ( Filter.Tendsto.mul ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) <| tendsto_const_nhds.mul <| Real.continuous_cos.continuousAt.tendsto.comp <| Filter.Tendsto.mul tendsto_const_nhds hseq.2 ) tendsto_const_nhds _ ) <| Complex.continuous_exp.continuousAt.tendsto.comp <| Filter.Tendsto.mul ( Complex.continuous_ofReal.continuousAt.tendsto.comp hseq.2 ) tendsto_const_nhds using 2 <;> norm_num
        · cases hθ' <;> simp +decide [ *, lemniscatePetalCurve ]
          · ring_nf; norm_num [ mul_div, mul_comm, show n ≠ 0 by linarith ]
          · ring_nf; norm_num [ mul_div, show n ≠ 0 by linarith ]
            norm_num [ mul_div, mul_comm, ne_of_gt ( zero_lt_one.trans_le hn ) ]
        · exact Or.inr hn
    · have h_seq : ∀ ε : ℝ, 0 < ε → ε < 1 → (((1 - ε) * (2 * Real.cos (n * θ))) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I) ∈ connectedComponentIn (OmegaSet (modelPoly n)) 1 := by
        grind +suggestions
      refine ⟨ fun k => ( ( ( 1 - 1 / ( k + 2 ) ) * ( 2 * Real.cos ( n * θ ) ) ) ^ ( 1 / n : ℝ ) : ℝ ) * Complex.exp ( θ * Complex.I ), ?_, ?_ ⟩ <;> norm_num
      · exact fun k => by simpa using h_seq ( ( k + 2 : ℝ ) ⁻¹ ) ( by positivity ) ( inv_lt_one_of_one_lt₀ ( by linarith ) )
      · refine Filter.Tendsto.mul ?_ tendsto_const_nhds
        convert Filter.Tendsto.comp ( Complex.continuous_ofReal.tendsto _ ) ( Filter.Tendsto.rpow ( Filter.Tendsto.mul ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) ) tendsto_const_nhds ) tendsto_const_nhds _ ) using 2 <;> norm_num
        · rw [ max_eq_right ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.1, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.2, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ) ) ]
        · exact Or.inr hn
  exact Set.image_subset_iff.mpr fun θ hθ => by obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq θ hθ; exact mem_closure_of_tendsto hseq₂ ( Filter.Eventually.of_forall hseq₁ )

/-! ## Sub-lemma: closure → Re ≥ 0 -/

/-- The closure of the component maps under z ↦ z^n into {Re ≥ 0}. -/
lemma component_closure_re_nonneg (n : ℕ) (_hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ closure (connectedComponentIn (OmegaSet (modelPoly n)) 1)) :
    0 ≤ (z ^ n).re := by
  rw [ mem_closure_iff_seq_limit ] at hz
  obtain ⟨x, hx⟩ := hz
  have h_seq : ∀ k, (x k ^ n).re > 0 := by
    have h_seq : ∀ k, x k ∈ OmegaSet (modelPoly n) := by
      exact fun k => connectedComponentIn_subset _ _ ( hx.1 k )
    intro k
    specialize h_seq k
    unfold OmegaSet modelPoly at h_seq
    norm_num [ Complex.normSq, Complex.norm_def ] at h_seq
    rw [ Real.sqrt_lt' ] at h_seq <;> nlinarith
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds ( Complex.continuous_re.continuousAt.tendsto.comp <| Filter.Tendsto.pow hx.2 _ ) fun k => le_of_lt <| h_seq k

/-! ## Helper: 0 is not in OmegaSet(z^n - 1) -/

lemma zero_not_in_omegaSet (n : ℕ) (hn : n ≥ 1) : (0 : ℂ) ∉ OmegaSet (modelPoly n) := by
  simp [OmegaSet, modelPoly]; norm_num [zero_pow (by omega : n ≠ 0)]

/-! ## Helper: z^n representation in terms of arg -/

lemma pow_re_eq_norm_mul_cos_arg (z : ℂ) (n : ℕ) :
    (z ^ n).re = ‖z‖ ^ n * Real.cos (↑n * Complex.arg z) := by
  rw [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring_nf;
  by_cases h : z = 0 <;> simp_all +decide [ ← Complex.exp_nat_mul ];
  · cases n <;> norm_num;
  · norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im ]

/-! ## Helper: cos(n * arg z) > 0 for z ∈ OmegaSet, z ≠ 0 -/

lemma omegaSet_cos_arg_pos (n : ℕ) (_hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ OmegaSet (modelPoly n)) (hz_ne : z ≠ 0) :
    0 < Real.cos (↑n * Complex.arg z) := by
  have h_cos_pos : 0 < (z ^ n).re := by
    have hz_ball : z ^ n ∈ Metric.ball (1 : ℂ) 1 := by
      unfold OmegaSet modelPoly at hz;
      simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.dist_eq] using hz;
    exact ball_one_one_sub_re_pos hz_ball;
  rw [ pow_re_eq_norm_mul_cos_arg ] at h_cos_pos ; aesop

/-! ## Helper: sector characterization without arg -/

/-
The set {z | z.re > ‖z‖ * c} is open for any c.
-/
lemma isOpen_re_gt_norm_mul (c : ℝ) : IsOpen {z : ℂ | z.re > ‖z‖ * c} := by
  exact isOpen_lt ( continuous_norm.mul continuous_const ) Complex.continuous_re

/-
The set {z | z.re < ‖z‖ * c} is open for any c.
-/
lemma isOpen_re_lt_norm_mul (c : ℝ) : IsOpen {z : ℂ | z.re < ‖z‖ * c} := by
  exact isOpen_lt ( Complex.continuous_re ) ( Continuous.mul ( continuous_norm ) continuous_const )

/-
No z ≠ 0 in OmegaSet(z^n - 1) has z.re = ‖z‖ * cos(π/(2n)).
    Because that would give |arg z| = π/(2n) hence cos(n * arg z) = 0,
    contradicting z^n ∈ B(1,1) ⊂ {Re > 0}.
-/
lemma omegaSet_no_boundary_arg (n : ℕ) (hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ OmegaSet (modelPoly n)) :
    z.re ≠ ‖z‖ * Real.cos (Real.pi / (2 * ↑n)) := by
  -- Assume z ≠ 0 and z.re = ‖z‖ * cos(π/(2n)).
  by_cases hz_ne_zero : z ≠ 0;
  · intro h_eq
    have h_arg : |Complex.arg z| = Real.pi / (2 * n) := by
      have h_arg : Real.cos (Complex.arg z) = Real.cos (Real.pi / (2 * n)) := by
        rw [ Complex.cos_arg ] <;> aesop;
      have h_arg_abs : |Complex.arg z| = Real.pi / (2 * n) := by
        have h_arg_range : -Real.pi < Complex.arg z ∧ Complex.arg z ≤ Real.pi := by
          exact ⟨ Complex.neg_pi_lt_arg z, Complex.arg_le_pi z ⟩
        have h_arg_range' : 0 ≤ Real.pi / (2 * n) ∧ Real.pi / (2 * n) ≤ Real.pi / 2 := by
          exact ⟨ by positivity, by gcongr ; norm_cast ; linarith ⟩
        have h_arg_abs : Real.cos (|Complex.arg z|) = Real.cos (Real.pi / (2 * n)) := by
          cases abs_cases z.arg <;> simp +decide [ * ];
        exact Real.injOn_cos ⟨ by cases abs_cases z.arg <;> linarith, by cases abs_cases z.arg <;> linarith ⟩ ⟨ by cases abs_cases z.arg <;> linarith, by cases abs_cases z.arg <;> linarith ⟩ h_arg_abs;
      exact h_arg_abs;
    have h_cos_arg : Real.cos (↑n * Complex.arg z) = 0 := by
      cases abs_cases ( Complex.arg z ) <;> simp_all +decide [ div_eq_mul_inv ];
      · ring_nf; norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hn ) ];
        norm_num [ mul_div ];
      · rw [ show ( n : ℝ ) * z.arg = - ( Real.pi / 2 ) by nlinarith [ Real.pi_pos, mul_inv_cancel₀ ( by positivity : ( n : ℝ ) ≠ 0 ), mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 : ℝ ) ≠ 0 ) ] ] ; norm_num;
    exact absurd h_cos_arg ( ne_of_gt ( omegaSet_cos_arg_pos n hn z hz hz_ne_zero ) );
  · exact absurd hz ( by rw [ not_ne_iff.mp hz_ne_zero ] ; exact zero_not_in_omegaSet n hn )

/-
The component of OmegaSet containing 1 is in the "positive sector"
    {z | z.re > ‖z‖ * cos(π/(2n))}.
-/
lemma component_in_positive_sector (n : ℕ) (hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ connectedComponentIn (OmegaSet (modelPoly n)) 1) :
    z.re > ‖z‖ * Real.cos (Real.pi / (2 * ↑n)) := by
  -- Apply the lemma that states the connected component is contained in the positive sector.
  have h_pos_sector : connectedComponentIn (OmegaSet (modelPoly n)) 1 ⊆ {z : ℂ | z.re > ‖z‖ * Real.cos (Real.pi / (2 * n))} := by
    apply IsPreconnected.subset_left_of_subset_union;
    any_goals exact { z : ℂ | z.re < ‖z‖ * Real.cos ( Real.pi / ( 2 * n ) ) };
    any_goals exact isOpen_re_gt_norm_mul _;
    · exact isOpen_re_lt_norm_mul _;
    · grind +revert;
    · exact fun x hx => lt_or_gt_of_ne ( omegaSet_no_boundary_arg n hn x <| connectedComponentIn_subset _ _ hx ) |> Or.symm;
    · refine ⟨ 1, ?_, ?_ ⟩ <;> norm_num;
      · exact mem_connectedComponentIn ( by norm_num [ OmegaSet, modelPoly ] );
      · nlinarith [ Real.sin_sq_add_cos_sq ( Real.pi / ( 2 * n ) ), Real.sin_pos_of_pos_of_lt_pi ( by positivity ) ( by rw [ div_lt_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] : Real.pi / ( 2 * n ) < Real.pi ) ];
    · exact isPreconnected_connectedComponentIn;
  exact h_pos_sector hz

/-! ## Helper: arg bound for points in the component (open interval) -/

/-
For z in the connected component of OmegaSet(z^n-1) containing 1,
    Complex.arg z ∈ (-π/(2n), π/(2n)).

    Follows from component_in_positive_sector: z.re > ‖z‖ * cos(π/(2n)) > 0
    implies cos(arg z) > cos(π/(2n)), hence |arg z| < π/(2n).
-/
lemma component_arg_strict_bound (n : ℕ) (hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ connectedComponentIn (OmegaSet (modelPoly n)) 1) :
    Complex.arg z ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) := by
  have h_arg : Real.cos (Complex.arg z) > Real.cos (Real.pi / (2 * n)) := by
    have h_cos_arg : z.re > ‖z‖ * Real.cos (Real.pi / (2 * n)) := by
      exact component_in_positive_sector n hn z hz
    by_cases h : z = 0 <;> simp_all +decide [ Complex.cos_arg ];
    rwa [ lt_div_iff₀' ( norm_pos_iff.mpr h ) ];
  have h_arg_abs : |Complex.arg z| < Real.pi / (2 * n) := by
    have h_arg_abs : Real.cos (|Complex.arg z|) > Real.cos (Real.pi / (2 * n)) := by
      aesop;
    contrapose! h_arg_abs;
    exact Real.cos_le_cos_of_nonneg_of_le_pi ( by positivity ) ( by cases abs_cases z.arg <;> linarith [ Real.pi_pos, Complex.neg_pi_lt_arg z, Complex.arg_le_pi z ] ) h_arg_abs;
  exact abs_lt.mp h_arg_abs

/-! ## Key sub-lemma: arg bound for closure of component -/

/-
Points z ≠ 0 in the closure of the component containing 1 satisfy
    Complex.arg z ∈ [-π/(2n), π/(2n)].

    Extends component_arg_strict_bound to the closure by continuity of arg
    (arg is continuous at z since z ≠ 0 and z.re ≥ 0, putting z in slitPlane).
-/
lemma component_closure_arg_bound (n : ℕ) (hn : n ≥ 1)
    (z : ℂ) (hz : z ∈ closure (connectedComponentIn (OmegaSet (modelPoly n)) 1))
    (hz_ne : z ≠ 0) :
    Complex.arg z ∈ Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) := by
  obtain ⟨ seq, hseq ⟩ := mem_closure_iff_seq_limit.mp hz;
  -- Since $z_k.re > ‖z_k‖ * cos(π/(2n))$, we have $z_k.re > 0$.
  have h_re_pos : ∀ k, 0 < (seq k).re := by
    intro k
    have h_re_pos : (seq k).re > ‖seq k‖ * Real.cos (Real.pi / (2 * n)) := by
      exact component_in_positive_sector n hn _ ( hseq.1 k );
    exact lt_of_le_of_lt ( mul_nonneg ( norm_nonneg _ ) ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ], by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩ ) ) h_re_pos;
  -- Since $z_k.re > 0$, we have $z_k.arg \in (-π/2, π/2)$.
  have h_arg_bounds : ∀ k, Complex.arg (seq k) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro k; exact ⟨by
    rw [ Complex.neg_pi_div_two_lt_arg_iff ] ; aesop, by
      rw [ Complex.arg_lt_pi_div_two_iff ] ; aesop⟩;
  -- Since $z_k.arg \in (-π/2, π/2)$, we have $z_k.arg \to z.arg$.
  have h_arg_tendsto : Filter.Tendsto (fun k => Complex.arg (seq k)) Filter.atTop (nhds (Complex.arg z)) := by
    convert Complex.continuousAt_arg _ |> Filter.Tendsto.comp <| hseq.2 using 1;
    simp_all +decide [ Complex.slitPlane ];
    contrapose! hz_ne;
    exact Complex.ext ( by norm_num; linarith [ show z.re ≥ 0 from le_of_tendsto_of_tendsto' tendsto_const_nhds ( Complex.continuous_re.continuousAt.tendsto.comp hseq.2 ) fun k => le_of_lt ( h_re_pos k ) ] ) ( by norm_num [ hz_ne ] );
  -- Since $z_k.arg \in (-π/(2n), π/(2n))$, we have $z_k.arg \to z.arg$.
  have h_arg_bounds : ∀ k, Complex.arg (seq k) ∈ Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n)) := by
    exact fun k => component_arg_strict_bound n hn _ ( hseq.1 k );
  exact ⟨ le_of_tendsto_of_tendsto' tendsto_const_nhds h_arg_tendsto fun k => le_of_lt ( h_arg_bounds k |>.1 ), le_of_tendsto_of_tendsto' h_arg_tendsto tendsto_const_nhds fun k => le_of_lt ( h_arg_bounds k |>.2 ) ⟩

/-! ## Main theorem: frontier = petal curve image -/

/-
The frontier of the component of OmegaSet(z^n-1) containing 1 equals
    the image of the lemniscate petal curve.
-/
theorem frontier_component_one_eq_lemniscate_arc' (n : ℕ) (hn : n ≥ 1) :
    frontier (connectedComponentIn (OmegaSet (modelPoly n)) 1) =
      lemniscatePetalCurve n '' Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) := by
  apply Set.Subset.antisymm
  · -- ⊆ direction: frontier ⊆ image
    intro z hz
    have h_norm : ‖(modelPoly n).eval z‖ = 1 :=
      frontier_component_sub_lemniscate' (modelPoly n) 1 (by simp [OmegaSet, modelPoly]) hz
    have h_re : 0 ≤ (z ^ n).re :=
      component_closure_re_nonneg n hn z hz.1
    by_cases hz_ne : z = 0
    · -- z = 0: γ(π/(2n)) = 0
      subst hz_ne
      refine ⟨Real.pi / (2 * ↑n), ⟨?_, le_refl _⟩, ?_⟩
      · have : (0 : ℝ) < Real.pi / (2 * ↑n) := by positivity
        linarith
      · unfold lemniscatePetalCurve
        rw [show (↑n : ℝ) * (Real.pi / (2 * ↑n)) = Real.pi / 2 from by
          field_simp]
        simp only [Real.cos_pi_div_two, mul_zero, max_self,
          Real.zero_rpow (show (1 : ℝ) / ↑n ≠ 0 by positivity),
          Complex.ofReal_zero, zero_mul]
    · -- z ≠ 0: use arg bound
      have h_arg := component_closure_arg_bound n hn z hz.1 hz_ne
      -- z = ‖z‖ · exp(i · arg z), and from |z^n - 1| = 1 + arg bound, z = γ(arg z)
      refine ⟨ Complex.arg z, h_arg, ?_ ⟩;
      -- From ‖z^n - 1‖ = 1: expand to get ‖z‖^{2n} - 2*‖z‖^n*cos(nθ) + 1 = 1.
      -- So ‖z‖^n(‖z‖^n - 2cos(nθ)) = 0. Since ‖z‖ > 0, ‖z‖^n = 2cos(nθ).
      have h_norm_eq : ‖z‖ ^ n = 2 * Real.cos (n * Complex.arg z) := by
        have h_norm_eq : ‖z‖ ^ (2 * n) - 2 * ‖z‖ ^ n * Real.cos (n * Complex.arg z) + 1 = 1 := by
          have h_norm_eq : ‖(z ^ n) - 1‖ ^ 2 = 1 := by
            simp_all +decide [ modelPoly ];
          convert h_norm_eq using 1 ; norm_num [ Complex.normSq, Complex.sq_norm ] ; ring_nf;
          rw [ ← Complex.norm_mul_exp_arg_mul_I z ] ; ring_nf ; norm_num [ ← Complex.exp_nat_mul, Complex.exp_re, Complex.exp_im ] ; ring_nf;
          norm_cast ; norm_num [ Real.sin_sq, pow_mul ] ; ring;
        exact mul_left_cancel₀ ( pow_ne_zero n ( norm_ne_zero_iff.mpr hz_ne ) ) ( by linear_combination' h_norm_eq );
      -- Since ‖z‖^n = 2cos(nθ), we have ‖z‖ = (2cos(nθ))^{1/n}.
      have h_norm_eq' : ‖z‖ = (2 * Real.cos (n * Complex.arg z)) ^ (1 / n : ℝ) := by
        rw [ ← h_norm_eq, ← Real.rpow_natCast, ← Real.rpow_mul ( norm_nonneg _ ), mul_one_div_cancel ( by positivity ), Real.rpow_one ];
      unfold lemniscatePetalCurve;
      rw [ max_eq_right ( by nlinarith [ show 0 ≤ ‖z‖ ^ n by positivity ] ), ← h_norm_eq', Complex.norm_mul_exp_arg_mul_I ]
  · -- ⊇ direction: image ⊆ frontier
    intro z ⟨θ, hθ, hθ_eq⟩
    rw [frontier_eq_closure_inter_closure]
    constructor
    · exact petal_curve_sub_closure n hn ⟨θ, hθ, hθ_eq⟩
    · rw [← hθ_eq]
      apply subset_closure
      change lemniscatePetalCurve n θ ∉ connectedComponentIn (OmegaSet (modelPoly n)) 1
      intro hc
      have h1 : lemniscatePetalCurve n θ ∈ OmegaSet (modelPoly n) :=
        connectedComponentIn_subset _ _ hc
      have h2 : ‖(modelPoly n).eval (lemniscatePetalCurve n θ)‖ < 1 := h1
      have h3 : ‖(modelPoly n).eval (lemniscatePetalCurve n θ)‖ = 1 :=
        lemniscatePetalCurve_on_lemniscate n hn θ hθ
      linarith

end Erdos1044


/-! ### From ArcLength.lean -/

/-
  Arc-length decomposition for the lemniscate boundary measure.

  This file decomposes `component_boundary_length_eq_lemniscateLength`
  into smaller honest sub-lemmas, isolating the key mathematical
  content at each step:

  A. Frontier identification:
     - `frontier_component_sub_lemniscate`: frontier ⊆ {|f(z)| = 1} ✅
     - `frontier_component_one_eq_lemniscate_arc`: frontier = image of petal curve

  B. Arc-length formula (general, not in Mathlib):
     - `hausdorffMeasure_curve_eq_integral`: μH[1](γ([a,b])) = ∫ ‖γ'‖

  C. Lemniscate integral:
     - `norm_deriv_lemniscatePetalCurve`: |γ'(θ)| = 2·(2cos(nθ))^{1/n-1} ✅
     - `integral_cos_rpow_eq_betaFn`: trigonometric Beta integral ✅
     - `lemniscate_arc_integral_eq`: ∫ |γ'| = lemniscateLength n ✅
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Sub-lemma A: Frontier of component lies on the lemniscate -/

/-- The frontier of any connected component of OmegaSet(f) is contained
    in the level set {z : ‖f.eval z‖ = 1}.

    Proof sketch: The closure is contained in {‖f(z)‖ ≤ 1} (by continuity),
    while the frontier is in (OmegaSet f)ᶜ = {‖f(z)‖ ≥ 1} (since OmegaSet is open
    and the component is a connected component of this open set). -/
lemma frontier_component_sub_lemniscate (f : Polynomial ℂ) (z : ℂ)
    (hz : z ∈ OmegaSet f) :
    frontier (connectedComponentIn (OmegaSet f) z) ⊆
      {w : ℂ | ‖f.eval w‖ = 1} := by
  -- The frontier of any connected component of OmegaSet f is contained in the level set {z : ‖f.eval z‖ = 1}.
  intros w hw
  have h_closure : w ∈ closure (OmegaSet f) := by
    exact closure_mono ( connectedComponentIn_subset _ _ ) hw.1
  have h_compl : w ∉ OmegaSet f := by
    intro hw_in_OmegaSet_f
    have hw_in_connectedComponent : w ∈ connectedComponentIn (OmegaSet f) z := by
      have hw_in_connectedComponent : IsPreconnected (connectedComponentIn (OmegaSet f) z ∪ {w}) := by
        rw [ isPreconnected_iff_subset_of_disjoint_closed ]
        intro u v hu hv huv huv_empty
        have h_connectedComponent : connectedComponentIn (OmegaSet f) z ⊆ u ∨ connectedComponentIn (OmegaSet f) z ⊆ v := by
          have h_connectedComponent : IsPreconnected (connectedComponentIn (OmegaSet f) z) := by
            exact isPreconnected_connectedComponentIn
          contrapose! h_connectedComponent
          simp_all +decide [ IsPreconnected, Set.subset_def ]
          use uᶜ, isOpen_compl_iff.mpr hu, vᶜ, isOpen_compl_iff.mpr hv
          simp_all +decide [ Set.ext_iff, Set.Nonempty ]
          grind +ring
        rcases h_connectedComponent with h | h <;> simp_all +decide [ Set.subset_def ]
        · exact Or.inl <| hu.closure_subset_iff.mpr ( by aesop ) <| by simpa using hw.1
        · exact Or.inr ( by exact closure_minimal ( show connectedComponentIn ( OmegaSet f ) z ⊆ v from fun x hx => h x hx ) hv ( frontier_subset_closure hw ) )
      have hw_in_connectedComponent : IsPreconnected (connectedComponentIn (OmegaSet f) z ∪ {w}) ∧ connectedComponentIn (OmegaSet f) z ∪ {w} ⊆ OmegaSet f := by
        exact ⟨ hw_in_connectedComponent, Set.union_subset ( connectedComponentIn_subset _ _ ) ( Set.singleton_subset_iff.mpr hw_in_OmegaSet_f ) ⟩
      have hw_in_connectedComponent : connectedComponentIn (OmegaSet f) z ∪ {w} ⊆ connectedComponentIn (OmegaSet f) z := by
        grind +suggestions
      exact hw_in_connectedComponent ( Set.mem_union_right _ ( Set.mem_singleton _ ) )
    exact hw.2 ( mem_interior_iff_mem_nhds.mpr ( Filter.mem_of_superset ( IsOpen.mem_nhds ( omegaSet_isOpen f |> IsOpen.connectedComponentIn ) hw_in_connectedComponent ) fun x hx => hx ) )
  have h_eq : ‖f.eval w‖ = 1 := by
    rw [ mem_closure_iff_seq_limit ] at h_closure
    exact le_antisymm ( le_of_tendsto_of_tendsto' ( Filter.Tendsto.norm ( f.continuous.continuousAt.tendsto.comp h_closure.choose_spec.2 ) ) tendsto_const_nhds fun n => le_of_lt ( h_closure.choose_spec.1 n ) ) ( le_of_not_gt fun h => h_compl <| by simpa using h )
  exact h_eq

/-- The frontier of the component of OmegaSet(z^n - 1) containing 1 equals
    the image of the lemniscate petal curve on [-π/(2n), π/(2n)].

    This identifies the topological frontier with the specific parametric
    lemniscate arc. The proof requires:
    - The component containing 1 is the petal {z : |z^n-1| < 1, arg(z) ∈ (-π/n, π/n)}
    - The frontier of this petal is the lemniscate arc
    - The petal curve parametrizes this arc -/
lemma frontier_component_one_eq_lemniscate_arc (n : ℕ) (hn : n ≥ 1) :
    frontier (connectedComponentIn (OmegaSet (modelPoly n)) 1) =
      lemniscatePetalCurve n '' Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) :=
  frontier_component_one_eq_lemniscate_arc' n hn

/-! ## Sub-lemma B: Arc-length formula (general) -/

/-
Upper bound: μH[1](γ([a,b])) ≤ ∫ ‖γ'‖.
    Proof: γ is Lipschitz on [a,b] (bounded derivative), and for Lipschitz
    maps f: ℝ → ℂ, μH[1](f(S)) ≤ K · μH[1](S) where K is the Lipschitz constant.
    Taking the infimum over partitions with local Lipschitz constants gives the bound.
-/
lemma hausdorffMeasure_curve_le_integral {a b : ℝ} (hab : a < b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ContinuousOn (fun t => ‖deriv γ t‖) (Icc a b)) :
    μH[(1 : ℝ)] (γ '' Icc a b) ≤
      ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) := by
  refine le_trans ?_ ( ?_ : ENNReal.ofReal ( ∫ t in a..b, ‖deriv γ t‖ ) ≤ _ );
  · have := @MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum;
    specialize @this ℂ _ _ _ ℕ ( fun n => Fin ( n + 1 ) ) _ 1 ( γ '' Icc a b ) Filter.atTop ( fun n => ENNReal.ofReal ( ( b - a ) / ( n + 1 ) ) * ENNReal.ofReal ( SupSet.sSup ( Set.image ( fun t => ‖deriv γ t‖ ) ( Set.Icc a b ) ) + 1 ) ) _;
    · convert ENNReal.Tendsto.mul_const ( ENNReal.tendsto_ofReal ( tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) _ using 1;
      · norm_num;
      · norm_num;
    · refine le_trans
        (this
          (fun n i => γ '' Set.Icc ( a + ( b - a ) * i / ( n + 1 ) )
            ( a + ( b - a ) * ( i + 1 ) / ( n + 1 ) ))
          ?_ ?_) ?_;
      · refine Filter.Eventually.of_forall fun n i => ?_;
        refine le_trans ( ediam_curve_image_le_integral (a := a) (b := b)
          ?_ ?_ ?_ ?_ ?_ ?_ ?_ ) ?_;
        any_goals assumption;
        · linarith;
        · bound;
        · exact ⟨ by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * i ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * i ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩;
        · exact ⟨ by nlinarith [ show ( i : ℝ ) + 1 ≤ n + 1 by norm_cast; linarith [ Fin.is_lt i ], mul_div_cancel₀ ( ( b - a ) * ( i + 1 ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ show ( i : ℝ ) + 1 ≤ n + 1 by norm_cast; linarith [ Fin.is_lt i ], mul_div_cancel₀ ( ( b - a ) * ( i + 1 ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩;
        · rw [ ← ENNReal.ofReal_mul ( by exact div_nonneg ( sub_nonneg.mpr hab.le ) ( by positivity ) ) ];
          refine ENNReal.ofReal_le_ofReal ?_;
          refine le_trans
            (b := ∫ u in a + (b - a) * i / (n + 1)..a + (b - a) * (i + 1) / (n + 1),
              (fun _ : ℝ => sSup ( Set.image ( fun t => ‖deriv γ t‖ ) ( Set.Icc a b ) ) + 1) u)
            (intervalIntegral.integral_mono_on
              (g := fun _ : ℝ => sSup ( Set.image ( fun t => ‖deriv γ t‖ ) ( Set.Icc a b ) ) + 1)
              ?_ ?_ ?_ ?_) ?_;
          · bound;
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            refine hγ_deriv_cont.mono ?_;
            rw [ uIcc_of_le ( by rw [ add_div', add_div', div_le_div_iff_of_pos_right ] <;> nlinarith ) ];
            exact Set.Icc_subset_Icc ( by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * ( i : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ) ( by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * ( i + 1 : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] );
          · norm_num;
          · intro x hx;
            refine le_add_of_le_of_nonneg ( le_csSup ?_ ?_ ) zero_le_one;
            · exact IsCompact.bddAbove ( isCompact_Icc.image_of_continuousOn hγ_deriv_cont );
            · exact ⟨ x, ⟨ by nlinarith [ hx.1, show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * ( i : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ hx.2, show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * ( i + 1 : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩, rfl ⟩;
          · norm_num [ mul_div_assoc ];
            ring_nf; norm_num;
      · refine Filter.Eventually.of_forall fun n => ?_;
        intro x hx;
        obtain ⟨ y, hy, rfl ⟩ := hx;
        simp +zetaDelta at *;
        by_cases hy' : y = b;
        · refine ⟨ ⟨ n, by linarith ⟩, b, ?_, ?_ ⟩ <;> norm_num [ hy' ];
          exact ⟨ by rw [ add_div', div_le_iff₀ ] <;> nlinarith, by rw [ mul_div_cancel_right₀ _ ( by linarith ) ] ; linarith ⟩;
        · refine ⟨ ⟨ ⌊ ( y - a ) * ( n + 1 ) / ( b - a ) ⌋₊, ?_ ⟩, y, ?_, rfl ⟩;
          all_goals norm_num [ Nat.floor_lt', div_lt_iff₀, lt_div_iff₀, hab, hy, hy' ];
          · exact Nat.le_of_lt_succ <| by rw [ Nat.floor_lt', div_lt_iff₀ ] <;> norm_num <;> nlinarith [ mul_self_pos.mpr <| sub_ne_zero.mpr hy' ] ;
          · field_simp;
            constructor <;> nlinarith [ Nat.floor_le ( show 0 ≤ ( y - a ) * ( n + 1 ) / ( b - a ) by exact div_nonneg ( mul_nonneg ( sub_nonneg.mpr hy.1 ) ( by positivity ) ) ( sub_nonneg.mpr hab.le ) ), Nat.lt_floor_add_one ( ( y - a ) * ( n + 1 ) / ( b - a ) ), mul_div_cancel₀ ( ( y - a ) * ( n + 1 ) ) ( sub_ne_zero.mpr hab.ne' ) ];
      · -- Apply the lemma that bounds the diameter of the image of a subinterval.
        have h_diam_bound : ∀ n : ℕ, ∀ i : Fin (n + 1), Metric.ediam (γ '' Set.Icc (a + (b - a) * i / (n + 1)) (a + (b - a) * (i + 1) / (n + 1))) ≤ ENNReal.ofReal (∫ t in (a + (b - a) * i / (n + 1))..(a + (b - a) * (i + 1) / (n + 1)), ‖deriv γ t‖) := by
          intro n i;
          apply_rules [ ediam_curve_image_le_integral ];
          · exact hab.le;
          · bound;
          · exact ⟨ by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * i ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ show ( i : ℝ ) ≤ n by norm_cast; linarith [ Fin.is_le i ], div_mul_cancel₀ ( ( b - a ) * i ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩;
          · exact ⟨ by nlinarith [ show ( i : ℝ ) + 1 ≤ n + 1 by norm_cast; linarith [ Fin.is_lt i ], mul_div_cancel₀ ( ( b - a ) * ( i + 1 ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ], by nlinarith [ show ( i : ℝ ) + 1 ≤ n + 1 by norm_cast; linarith [ Fin.is_lt i ], mul_div_cancel₀ ( ( b - a ) * ( i + 1 ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ⟩;
        refine Filter.liminf_le_of_frequently_le ?_ ?_;
        · refine Filter.frequently_atTop.mpr fun n => ?_;
          refine ⟨ n, le_rfl, ?_ ⟩;
          refine le_trans ( Finset.sum_le_sum fun i _ => by simpa using h_diam_bound n i ) ?_;
          rw [ ← ENNReal.ofReal_sum_of_nonneg ];
          · convert ENNReal.ofReal_le_ofReal ?_;
            have h_sum_integral : ∑ i ∈ Finset.range (n + 1), ∫ t in (a + (b - a) * i / (n + 1))..(a + (b - a) * (i + 1) / (n + 1)), ‖deriv γ t‖ = ∫ t in a..b, ‖deriv γ t‖ := by
              convert intervalIntegral.sum_integral_adjacent_intervals _ <;> norm_num;
              · rw [ mul_div_cancel_right₀ _ ( by positivity ), add_sub_cancel ];
              · intro k hk;
                apply_rules [ ContinuousOn.intervalIntegrable ];
                refine hγ_deriv_cont.mono ?_;
                rw [ uIcc_of_le ( by rw [ add_div', add_div', div_le_div_iff_of_pos_right ] <;> nlinarith [ show ( k : ℝ ) ≤ n by norm_cast ] ) ];
                exact Set.Icc_subset_Icc ( by nlinarith [ show ( k : ℝ ) ≤ n by norm_cast, mul_div_cancel₀ ( ( b - a ) * k ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ) ( by nlinarith [ show ( k : ℝ ) ≤ n by norm_cast, mul_div_cancel₀ ( ( b - a ) * ( k + 1 ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] );
            rw [ ← h_sum_integral, Finset.sum_range ];
          · exact fun _ _ => intervalIntegral.integral_nonneg ( by nlinarith [ show ( ↑‹Fin ( n + 1 ) › : ℝ ) + 1 ≤ n + 1 by norm_cast; linarith [ Fin.is_lt ‹_› ], mul_div_cancel₀ ( ( b - a ) * ( ↑‹Fin ( n + 1 ) › : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ), mul_div_cancel₀ ( ( b - a ) * ( ↑‹Fin ( n + 1 ) › + 1 : ℝ ) ) ( by linarith : ( n : ℝ ) + 1 ≠ 0 ) ] ) fun _ _ => norm_nonneg _;
        · refine ⟨ 0, Filter.eventually_atTop.mpr ⟨ 0, fun n hn => ?_ ⟩ ⟩ ; aesop;
  · rfl

/-- Lower bound: μH[1](γ([a,b])) ≥ ∫ ‖γ'‖ for injective curves.
    Proof: For any partition, the sum of distances Σ ‖γ(t_{k+1}) - γ(t_k)‖ ≤ μH[1](γ([a,b]))
    (since μH[1] of a connected set ≥ diameter ≥ distance between endpoints, and
    by injectivity the sub-arcs contribute additively). -/
lemma hausdorffMeasure_curve_ge_integral {a b : ℝ} (hab : a < b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_inj : InjOn γ (Ioo a b))
    (_hγ_deriv_cont : ContinuousOn (fun t => ‖deriv γ t‖) (Icc a b))
    (hγ_deriv_cont' : ContinuousOn (deriv γ) (Icc a b)) :
    ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) ≤
      μH[(1 : ℝ)] (γ '' Icc a b) :=
  le_trans (integral_le_eVariationOn hab hγ_cont hγ_diff hγ_deriv_cont')
    (eVariationOn_le_hausdorffMeasure_injective hab hγ_cont hγ_inj)

/-- The arc-length formula for C¹ curves: the 1-dimensional Hausdorff measure
    of the image of a continuous curve with differentiable derivative
    equals the integral of the norm of the derivative, provided the curve
    is injective on the open interval.

    This is a standard result in geometric measure theory that is not
    currently in Mathlib. The proof combines:
    - Upper bound via Lipschitz estimate on small intervals
    - Lower bound via injectivity and pushforward density

    We allow γ(a) = γ(b) (endpoints may coincide, as for lemniscate arcs). -/
lemma hausdorffMeasure_curve_eq_integral {a b : ℝ} (hab : a < b)
    {γ : ℝ → ℂ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_inj : InjOn γ (Ioo a b))
    (hγ_deriv_cont : ContinuousOn (fun t => ‖deriv γ t‖) (Icc a b))
    (hγ_deriv_cont' : ContinuousOn (deriv γ) (Icc a b)) :
    μH[(1 : ℝ)] (γ '' Icc a b) =
      ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
  le_antisymm
    (hausdorffMeasure_curve_le_integral hab hγ_cont hγ_diff hγ_deriv_cont)
    (hausdorffMeasure_curve_ge_integral hab hγ_cont hγ_diff hγ_inj hγ_deriv_cont hγ_deriv_cont')

/-! ## Sub-lemma C: Lemniscate integral computation -/

/-- The norm of the derivative of the lemniscate petal curve.
    For γ(θ) = (2cos(nθ))^{1/n} · e^{iθ}, we have
    ‖γ'(θ)‖ = 2 · (2cos(nθ))^{1/n - 1}.

    Computation: γ = r·e^{iθ} with r = (2cos(nθ))^{1/n}.
    γ' = (r' + ir)·e^{iθ}, so |γ'|² = r'² + r².
    r' = -2sin(nθ)·(2cos(nθ))^{1/n - 1}
    r'² + r² = 4·(2cos(nθ))^{2/n - 2}
    |γ'| = 2·(2cos(nθ))^{1/n - 1}
-/
lemma norm_deriv_lemniscatePetalCurve (n : ℕ) (hn : n ≥ 1) (θ : ℝ)
    (hθ : θ ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n))) :
    ‖deriv (lemniscatePetalCurve n) θ‖ =
      2 * (2 * Real.cos (↑n * θ)) ^ ((1 : ℝ) / ↑n - 1) := by
  convert congr_arg Norm.norm ( HasDerivAt.deriv <| HasDerivAt.mul ( HasDerivAt.ofReal_comp ( HasDerivAt.rpow_const ( HasDerivAt.congr_of_eventuallyEq ( HasDerivAt.const_mul 2 <| HasDerivAt.cos <| HasDerivAt.const_mul ( n : ℝ ) <| hasDerivAt_id θ ) <| Filter.eventuallyEq_of_mem ( Ioo_mem_nhds hθ.1 hθ.2 ) fun x hx => max_eq_right ?_ ) ?_ ) ) <| HasDerivAt.comp _ ( Complex.hasDerivAt_exp _ ) <| HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ _ ) using 1 <;> norm_num
  · norm_num [ Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im ]
    norm_cast ; norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hn ) ]
    rw [ max_eq_right ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, hθ.1, hθ.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, hθ.1, hθ.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ) ) ] ; ring_nf
    rw [ eq_comm, Real.sqrt_eq_iff_mul_self_eq ]
    · rw [ Real.sin_sq, Real.sin_sq ] ; ring_nf
      rw [ show ( n : ℝ ) ⁻¹ = -1 + ( n : ℝ ) ⁻¹ + 1 by ring, Real.rpow_add_one ] <;> ring_nf ; norm_num
      exact ne_of_gt ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.2 ] ⟩ )
    · positivity
    · exact mul_nonneg ( Real.rpow_nonneg ( mul_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.2 ] ⟩ ) zero_le_two ) _ ) zero_le_two
  · exact Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ hx.1, hx.2, Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ hx.1, hx.2, Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩
  · exact Or.inl ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.1, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hθ.2, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ )

/-
The trigonometric Beta integral: for α > -1,
    ∫_0^{π/2} cos(θ)^α dθ = betaFn(1/2, (α+1)/2) / 2.

    Proof: substitute x = sin²(θ), dx = 2sin(θ)cos(θ)dθ, giving
    ∫_0^1 x^{-1/2}(1-x)^{(α-1)/2}/(2) dx
    = (1/2) · ∫_0^1 x^{1/2-1}(1-x)^{(α+1)/2-1} dx
    = (1/2) · B(1/2, (α+1)/2)
    = (1/2) · Γ(1/2)·Γ((α+1)/2)/Γ((α+1)/2 + 1/2).
-/
lemma integral_cos_rpow_eq_betaFn (α : ℝ) (hα : α > -1) :
    ∫ θ in (0 : ℝ)..(Real.pi / 2),
      (Real.cos θ) ^ α = betaFn (1/2) ((α + 1) / 2) / 2 := by
  -- By substituting $x = \sin^2(\theta)$, we can transform the integral into the Beta function form.
  have h_subst : ∫ θ in (0 : ℝ)..Real.pi / 2, Real.cos θ ^ α = (1 / 2) * ∫ x in (0 : ℝ)..1, x ^ (-1 / 2 : ℝ) * (1 - x) ^ ((α - 1) / 2 : ℝ) := by
    -- Apply the substitution $x = \sin^2(\theta)$ to transform the integral.
    have h_subst : ∫ θ in (0)..Real.pi / 2, Real.cos θ ^ α = ∫ x in (0)..1, (Real.cos (Real.arcsin (Real.sqrt x))) ^ α * (1 / (2 * Real.sqrt (x * (1 - x)))) := by
      rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le, intervalIntegral.integral_of_le zero_le_one ];
      have h_subst : ∫ x in (Set.Ioo 0 (Real.pi / 2)), (Real.cos x) ^ α = ∫ x in (Set.image (fun θ => Real.sin θ ^ 2) (Set.Ioo 0 (Real.pi / 2))), (Real.cos (Real.arcsin (Real.sqrt x))) ^ α * (1 / (2 * Real.sqrt (x * (1 - x)))) := by
        rw [ MeasureTheory.integral_image_eq_integral_abs_deriv_smul ];
        any_goals intro x hx; exact DifferentiableAt.hasDerivAt ( DifferentiableAt.pow ( Real.differentiableAt_sin ) 2 ) |> HasDerivAt.hasDerivWithinAt;
        · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_;
          norm_num [ Real.sin_sq, Real.cos_arcsin ];
          rw [ Real.sq_sqrt ( by nlinarith [ Real.cos_sq' x ] ) ] ; ring_nf;
          rw [ show Real.cos x ^ 2 - Real.cos x ^ 4 = ( Real.cos x ^ 2 ) * ( 1 - Real.cos x ^ 2 ) by ring, Real.sqrt_mul ( sq_nonneg _ ), Real.sqrt_sq ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, hx.1 ], by linarith [ Real.pi_pos, hx.2 ] ⟩ ) ] ; ring_nf;
          rw [ ← Real.sin_sq, Real.sqrt_sq_eq_abs ] ; ring_nf;
          simp +decide [ mul_assoc, mul_comm, ne_of_gt ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos, hx.1 ], hx.2 ⟩ ), ne_of_gt ( Real.sin_pos_of_mem_Ioo ⟨ hx.1, by linarith [ Real.pi_pos, hx.2 ] ⟩ ), abs_of_pos ( Real.cos_pos_of_mem_Ioo ⟨ by linarith [ Real.pi_pos, hx.1 ], hx.2 ⟩ ), abs_of_pos ( Real.sin_pos_of_mem_Ioo ⟨ hx.1, by linarith [ Real.pi_pos, hx.2 ] ⟩ ) ];
        · exact measurableSet_Ioo;
        · exact fun x hx y hy hxy => Real.injOn_sin ⟨ by linarith [ Real.pi_pos, hx.1 ], by linarith [ Real.pi_pos, hx.2 ] ⟩ ⟨ by linarith [ Real.pi_pos, hy.1 ], by linarith [ Real.pi_pos, hy.2 ] ⟩ <| by nlinarith [ Real.sin_pos_of_pos_of_lt_pi hx.1 <| by linarith [ Real.pi_pos, hx.2 ], Real.sin_pos_of_pos_of_lt_pi hy.1 <| by linarith [ Real.pi_pos, hy.2 ] ] ;
      rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo, h_subst ];
      rw [ show ( fun θ => Real.sin θ ^ 2 ) '' Ioo 0 ( Real.pi / 2 ) = Set.Ioo 0 1 from ?_ ];
      ext x
      simp [Set.mem_image];
      exact ⟨ fun ⟨ θ, hθ, hx ⟩ => ⟨ hx ▸ pow_pos ( Real.sin_pos_of_pos_of_lt_pi hθ.1 ( by linarith ) ) 2, hx ▸ by nlinarith [ Real.sin_sq_add_cos_sq θ, Real.cos_pos_of_mem_Ioo ⟨ by linarith, hθ.2 ⟩ ] ⟩, fun hx => ⟨ Real.arcsin ( Real.sqrt x ), ⟨ Real.arcsin_pos.2 ( Real.sqrt_pos.2 hx.1 ), by rw [ Real.arcsin_lt_pi_div_two ] ; nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt hx.1.le ] ⟩, by rw [ Real.sin_arcsin ] <;> nlinarith [ Real.sqrt_nonneg x, Real.sq_sqrt hx.1.le ] ⟩ ⟩;
    rw [ h_subst, ← intervalIntegral.integral_const_mul ];
    rw [ intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one ];
    rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_;
    rw [ Real.cos_arcsin ] ; ring_nf;
    rw [ Real.sq_sqrt hx.1.le ] ; rw [ show x - x ^ 2 = x * ( 1 - x ) by ring, Real.sqrt_mul hx.1.le ] ; norm_num [ Real.rpow_neg hx.1.le, Real.rpow_neg ( sub_nonneg.2 hx.2.le ) ] ; ring_nf;
    rw [ Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ( by linarith [ hx.1, hx.2 ] ), ← Real.rpow_neg ( by linarith [ hx.1, hx.2 ] ) ] ; ring_nf;
    rw [ ← Real.rpow_add ( by linarith [ hx.1, hx.2 ] ) ] ; ring_nf;
  -- Recognize that the integral is a Beta function with parameters $u = \frac{1}{2}$ and $v = \frac{\alpha + 1}{2}$.
  have h_beta : ∫ x in (0 : ℝ)..1, x ^ (-1 / 2 : ℝ) * (1 - x) ^ ((α - 1) / 2 : ℝ) = Complex.re (Complex.betaIntegral (1 / 2 : ℂ) ((α + 1) / 2 : ℂ)) := by
    rw [ Complex.betaIntegral ];
    convert rfl using 2 ; norm_num [ Complex.ofReal_cpow ] ; ring_nf;
    convert Complex.ofReal_re _;
    convert intervalIntegral.integral_ofReal using 1 ; norm_num;
    refine intervalIntegral.integral_congr fun x hx => ?_ ; norm_num [ Complex.ofReal_cpow, show x ≥ 0 from by norm_num at hx ; linarith, show ( 1 - x ) ≥ 0 from by norm_num at hx ; linarith ];
  have h_beta_eq : Complex.betaIntegral (1 / 2 : ℂ) ((α + 1) / 2 : ℂ) = (Real.Gamma (1 / 2) * Real.Gamma ((α + 1) / 2)) / Real.Gamma ((α + 1) / 2 + 1 / 2) := by
    convert Complex.betaIntegral_eq_Gamma_mul_div ( 1 / 2 : ℂ ) ( ( α + 1 ) / 2 : ℂ ) _ _ using 1 <;> norm_num;
    · rw [ ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal ] ; ring_nf;
      norm_num;
    · grind +splitIndPred;
  simp_all +decide [ betaFn ];
  ring_nf

/-
The arc-length integral of the lemniscate petal curve equals lemniscateLength n.

    ∫_{-π/(2n)}^{π/(2n)} 2·(2cos(nθ))^{1/n-1} dθ
    = (2/n) ∫_{-π/2}^{π/2} (2cos u)^{1/n-1} du       [u = nθ]
    = (2^{1/n}/n) ∫_{-π/2}^{π/2} cos^{1/n-1}(u) du
    = (2^{1/n}/n) · B(1/(2n), 1/2)                     [Euler Beta integral]
    = (2^{1/n}/n) · B(1/2, 1/(2n))                     [B symmetric]
    = lemniscateLength n
-/
lemma lemniscate_arc_integral_eq (n : ℕ) (hn : n ≥ 1) :
    ∫ θ in (-(Real.pi / (2 * ↑n)))..(Real.pi / (2 * ↑n)),
      ‖deriv (lemniscatePetalCurve n) θ‖ = lemniscateLength n := by
  have h_integral : ∫ θ in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) θ‖ = (2 / n) * ∫ u in (-(Real.pi / 2))..(Real.pi / 2), (2 * Real.cos u) ^ ((1 / n : ℝ) - 1) := by
    have h_integral : ∫ θ in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) θ‖ = ∫ θ in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), 2 * (2 * Real.cos (n * θ)) ^ ((1 : ℝ) / n - 1) := by
      rw [ intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos, show ( 0 : ℝ ) ≤ Real.pi / ( 2 * n ) by positivity ] ), MeasureTheory.integral_Ioc_eq_integral_Ioo ];
      rw [ intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos, show ( 0 : ℝ ) ≤ Real.pi / ( 2 * n ) by positivity ] ), MeasureTheory.integral_Ioc_eq_integral_Ioo ] ; exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => norm_deriv_lemniscatePetalCurve n hn x hx;
    convert h_integral using 1;
    rw [ intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left fun x => ( 2 * Real.cos x ) ^ ( 1 / ( n : ℝ ) - 1 ) ] <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hn ) ];
  have h_integral_symm : ∫ u in (-(Real.pi / 2))..(Real.pi / 2), (2 * Real.cos u) ^ ((1 / n : ℝ) - 1) = 2 * ∫ u in (0 : ℝ)..(Real.pi / 2), (2 * Real.cos u) ^ ((1 / n : ℝ) - 1) := by
    rw [ two_mul, ← intervalIntegral.integral_add_adjacent_intervals ];
    rw [ ← intervalIntegral.integral_comp_neg, neg_zero ];
    · norm_num;
    · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le ];
      · have h_integrable : MeasureTheory.IntegrableOn (fun u => (Real.cos u) ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u => (Real.sin u) ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
            have h_integrable : MeasureTheory.IntegrableOn (fun u => u ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
              exact ( intervalIntegral.intervalIntegrable_rpow' ( by linarith [ show ( 1 : ℝ ) / n > 0 by positivity ] ) ).1.mono_set ( Set.Ioo_subset_Ioc_self );
            have h_integrable : ∀ u ∈ Set.Ioo 0 (Real.pi / 2), (Real.sin u) ^ ((1 / n : ℝ) - 1) ≤ (2 / Real.pi) ^ ((1 / n : ℝ) - 1) * u ^ ((1 / n : ℝ) - 1) := by
              intros u hu
              have h_sin_le : Real.sin u ≥ (2 / Real.pi) * u := by
                exact le_trans ( by ring_nf; norm_num ) ( Real.mul_le_sin hu.1.le hu.2.le );
              rw [ ← Real.mul_rpow ( by positivity ) ( by linarith [ hu.1 ] ) ];
              exact Real.rpow_le_rpow_of_nonpos ( mul_pos ( by positivity ) hu.1 ) h_sin_le ( sub_nonpos_of_le <| by rw [ div_le_iff₀ ] <;> norm_cast ; linarith );
            refine MeasureTheory.Integrable.mono'
              (g := fun u => ( 2 / Real.pi ) ^ ( 1 / n - 1 : ℝ ) * u ^ ( 1 / n - 1 : ℝ ))
              ?_ ?_ ?_;
            · exact MeasureTheory.Integrable.const_mul ‹_› _;
            · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( Real.continuous_sin.measurable ) _ );
            · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with u hu using by rw [ Real.norm_of_nonneg ( Real.rpow_nonneg ( Real.sin_nonneg_of_nonneg_of_le_pi hu.1.le ( by linarith [ hu.2, Real.pi_pos ] ) ) _ ) ] ; exact h_integrable u hu;
          rw [ ← MeasureTheory.integrable_indicator_iff ( measurableSet_Ioo ) ] at *;
          convert h_integrable.comp_sub_left ( Real.pi / 2 ) using 1;
          ext; simp [Set.indicator];
          simp +decide only [and_comm, Real.sin_pi_div_two_sub];
        have h_integrable : MeasureTheory.IntegrableOn (fun u => (2 * Real.cos u) ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
          have h_integrable : MeasureTheory.IntegrableOn (fun u => 2 ^ ((1 / n : ℝ) - 1) * (Real.cos u) ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
            exact h_integrable.const_mul _;
          exact h_integrable.congr_fun ( fun x hx => by rw [ Real.mul_rpow ( by positivity ) ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, hx.1 ], by linarith [ Real.pi_pos, hx.2 ] ⟩ ) ] ) measurableSet_Ioo;
        convert h_integrable.comp_neg using 1 ; norm_num;
        norm_num [ Set.ext_iff ];
      · linarith [ Real.pi_pos ];
    · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le ];
      · refine MeasureTheory.Integrable.mono'
          (g := fun u => 2 ^ ( 1 / ( n : ℝ ) - 1 ) * ( Real.cos u ) ^ ( 1 / ( n : ℝ ) - 1 ))
          ?_ ?_ ?_;
        · refine MeasureTheory.Integrable.const_mul ?_ _;
          have h_integrable : MeasureTheory.IntegrableOn (fun u => Real.cos u ^ ((1 / n : ℝ) - 1)) (Set.Ioo 0 (Real.pi / 2)) := by
            have h_beta : ∫ u in (0 : ℝ)..(Real.pi / 2), Real.cos u ^ ((1 / n : ℝ) - 1) = betaFn (1 / 2) ((1 / n : ℝ) / 2) / 2 := by
              convert integral_cos_rpow_eq_betaFn _ _ using 1 <;> ring_nf;
              exact lt_add_of_pos_right _ ( by positivity )
            contrapose! h_beta;
            rw [ intervalIntegral.integral_of_le Real.pi_div_two_pos.le, MeasureTheory.integral_undef ];
            · exact ne_of_lt ( div_pos ( div_pos ( mul_pos ( Real.Gamma_pos_of_pos ( by norm_num ) ) ( Real.Gamma_pos_of_pos ( by positivity ) ) ) ( Real.Gamma_pos_of_pos ( by positivity ) ) ) zero_lt_two );
            · rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Ioc ] at *;
          aesop;
        · exact Measurable.aestronglyMeasurable ( by exact Measurable.pow_const ( measurable_const.mul ( Real.continuous_cos.measurable ) ) _ );
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using by rw [ Real.norm_of_nonneg ( Real.rpow_nonneg ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, hx.1 ], by linarith [ Real.pi_pos, hx.2 ] ⟩ ) ) _ ) ] ; rw [ Real.mul_rpow ( by positivity ) ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Real.pi_pos, hx.1 ], by linarith [ Real.pi_pos, hx.2 ] ⟩ ) ] ;
      · linarith [ Real.pi_pos ];
  have h_integral_cos : ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.cos u) ^ ((1 / n : ℝ) - 1) = betaFn (1 / 2) (1 / (2 * n)) / 2 := by
    convert integral_cos_rpow_eq_betaFn ( ( 1 / n : ℝ ) - 1 ) _ using 1 <;> ring_nf ; norm_num [ hn ];
    linarith;
  simp_all +decide [ lemniscateLength ];
  rw [ intervalIntegral.integral_congr fun x hx => by rw [ Real.mul_rpow ( by norm_num ) ( Real.cos_nonneg_of_mem_Icc ⟨ by linarith [ Set.mem_Icc.mp ( by simpa [ Real.pi_div_two_pos.le ] using hx ) ], by linarith [ Set.mem_Icc.mp ( by simpa [ Real.pi_div_two_pos.le ] using hx ) ] ⟩ ) ] ] ; norm_num [ Real.rpow_sub ] ; ring_nf;
  grind

end Erdos1044


/-! ### From PetalArcLength.lean -/

/-
  Arc-length computation for the lemniscate petal curve.

  This file proves that the Hausdorff 1-measure of the petal curve image
  equals ENNReal.ofReal (lemniscateLength n), using a truncation argument
  to handle the fact that the derivative may blow up at the endpoints.
-/

open Polynomial MeasureTheory Topology Set Metric Complex MeasureTheory.Measure

noncomputable section

namespace Erdos1044

/-! ## Petal curve properties -/

/-
The lemniscate petal curve is continuous on its defining interval.
-/
lemma petal_continuousOn (n : ℕ) (hn : n ≥ 1) :
    ContinuousOn (lemniscatePetalCurve n)
      (Icc (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n))) := by
        refine ContinuousOn.mul ?_ <| Continuous.continuousOn <| by continuity;
        refine Continuous.continuousOn ?_;
        exact Complex.continuous_ofReal.comp <| Continuous.rpow ( continuous_const.max <| continuous_const.mul <| Real.continuous_cos.comp <| by continuity ) continuous_const <| by continuity;

/-
The lemniscate petal curve is differentiable at every interior point.
-/
lemma petal_differentiableAt (n : ℕ) (hn : n ≥ 1) :
    ∀ t ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)),
      DifferentiableAt ℝ (lemniscatePetalCurve n) t := by
        have harg_mem : ∀ t ∈ Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)),
            (n : ℝ) * t ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
          intro t ht;
          have hn_pos : 0 < (n : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn);
          constructor;
          · calc
              -(Real.pi / 2) = (n : ℝ) * (-(Real.pi / (2 * n))) := by
                field_simp [hn_pos.ne']
              _ < (n : ℝ) * t := mul_lt_mul_of_pos_left ht.1 hn_pos
          · calc
              (n : ℝ) * t < (n : ℝ) * (Real.pi / (2 * n)) :=
                mul_lt_mul_of_pos_left ht.2 hn_pos
              _ = Real.pi / 2 := by
                field_simp [hn_pos.ne']
        intro t ht; refine DifferentiableAt.mul ?_ ?_ ;
        · refine DifferentiableAt.congr_of_eventuallyEq
            (f := fun θ => ↑ ( ( 2 * Real.cos ( n * θ ) ) ^ ( 1 / n : ℝ ) )) ?_ ?_;
          · refine Complex.ofRealCLM.differentiableAt.comp _ ?_;
            refine DifferentiableAt.rpow ?_ ?_ ?_;
            · fun_prop;
            · fun_prop;
            · exact ne_of_gt (mul_pos zero_lt_two (Real.cos_pos_of_mem_Ioo (harg_mem t ht)));
          · filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with θ hθ using by
              rw [ max_eq_right ( mul_nonneg zero_le_two
                (le_of_lt (Real.cos_pos_of_mem_Ioo (harg_mem θ hθ))) ) ] ;
        · exact Complex.differentiableAt_exp.comp _ ( differentiableAt_id.smul_const _ )

/-
The lemniscate petal curve is injective on the open interval.
    Since γ(θ) = r(θ)·exp(iθ) with r(θ) > 0 in the interior, different θ
    give different arguments, hence different points.
-/
lemma petal_injOn (n : ℕ) (hn : n ≥ 1) :
    InjOn (lemniscatePetalCurve n)
      (Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n))) := by
        intro x hx y hy h_eq;
        apply_fun Complex.arg at h_eq;
        unfold lemniscatePetalCurve at h_eq;
        rw [ Complex.arg_real_mul, Complex.arg_real_mul ] at h_eq;
        · rw [ Complex.exp_mul_I, Complex.exp_mul_I, Complex.arg_cos_add_sin_mul_I, Complex.arg_cos_add_sin_mul_I ] at h_eq;
          · exact h_eq;
          · constructor <;> nlinarith [ hx.1, hx.2, hy.1, hy.2, Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ];
          · constructor <;> nlinarith [ hx.1, hx.2, Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ];
        · exact Real.rpow_pos_of_pos ( lt_max_of_lt_right ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hy.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hy.2 ] ⟩ ) ) ) _;
        · exact Real.rpow_pos_of_pos ( lt_max_of_lt_right ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hx.1, hx.2, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, hx.1, hx.2, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ) ) ) _

/-
The petal curve value at the endpoints is 0.
-/
lemma petal_endpoint_zero (n : ℕ) (hn : n ≥ 1) :
    lemniscatePetalCurve n (-(Real.pi / (2 * ↑n))) = 0 ∧
    lemniscatePetalCurve n (Real.pi / (2 * ↑n)) = 0 := by
      unfold lemniscatePetalCurve;
      ring_nf; norm_num [ mul_assoc, mul_comm Real.pi _, hn, show n ≠ 0 by positivity ];
      norm_num [ mul_div, mul_comm ]

/-
On the interior of the interval, cos(n*θ) > 0, so the max is redundant and
    the curve is smooth. The derivative is continuous on the open interval.
-/
lemma petal_deriv_continuousOn_interior (n : ℕ) (hn : n ≥ 1) :
    ContinuousOn (deriv (lemniscatePetalCurve n))
      (Ioo (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n))) := by
        have h_cont_deriv : ContinuousOn (fun θ => deriv (fun θ => ((2 * Real.cos (n * θ)) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I)) θ) (Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n))) := by
          have h_cont_deriv : ∀ θ ∈ Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n)), deriv (fun θ => ((2 * Real.cos (n * θ)) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I)) θ = (deriv (fun θ => ((2 * Real.cos (n * θ)) ^ ((1 : ℝ) / n) : ℝ)) θ) * Complex.exp (θ * Complex.I) + ((2 * Real.cos (n * θ)) ^ ((1 : ℝ) / n) : ℝ) * Complex.exp (θ * Complex.I) * Complex.I := by
            intro θ hθ; convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.ofReal_comp ( hasDerivAt_deriv_iff.mpr ?_ ) ) ( HasDerivAt.comp θ ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) <| hasDerivAt_const _ _ ) ) ) using 1 <;> norm_num ; ring;
            exact DifferentiableAt.rpow ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Real.differentiableAt_cos.comp _ ( differentiableAt_id.const_mul _ ) ) ) ( by norm_num ) ( by exact ne_of_gt ( mul_pos zero_lt_two ( Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.1 ], by nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ), hθ.2 ] ⟩ ) ) );
          refine ContinuousOn.congr ?_ h_cont_deriv;
          refine ContinuousOn.add ?_ ?_;
          · refine ContinuousOn.mul ?_ ?_;
            · refine Complex.continuous_ofReal.comp_continuousOn ?_;
              refine ContinuousOn.congr
                (f := fun θ => ( 1 / n : ℝ ) *
                  ( 2 * Real.cos ( n * θ ) ) ^ ( ( 1 : ℝ ) / n - 1 ) *
                  ( -2 * n * Real.sin ( n * θ ) )) ?_ ?_;
              · refine ContinuousOn.mul ( ContinuousOn.mul continuousOn_const ?_ ) ?_;
                · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.rpow ( continuousAt_const.mul ( Real.continuous_cos.continuousAt.comp ( continuousAt_const.mul continuousAt_id ) ) ) continuousAt_const <| Or.inl <| ne_of_gt <| mul_pos zero_lt_two <| Real.cos_pos_of_mem_Ioo ⟨ by nlinarith [ Real.pi_pos, hx.1, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, hx.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ Real.pi ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩;
                · fun_prop;
              · intro θ hθ;
                have hcos_pos : 0 < Real.cos (θ * (n : ℝ)) * 2 := by
                  have harg : (n : ℝ) * θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
                    have hn_pos : 0 < (n : ℝ) := by
                      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn);
                    constructor;
                    · calc
                        -(Real.pi / 2) = (n : ℝ) * (-(Real.pi / (2 * n))) := by
                          field_simp [hn_pos.ne']
                        _ < (n : ℝ) * θ := mul_lt_mul_of_pos_left hθ.1 hn_pos
                    · calc
                        (n : ℝ) * θ < (n : ℝ) * (Real.pi / (2 * n)) :=
                          mul_lt_mul_of_pos_left hθ.2 hn_pos
                        _ = Real.pi / 2 := by
                          field_simp [hn_pos.ne']
                  exact mul_pos (by simpa [mul_comm] using Real.cos_pos_of_mem_Ioo harg) zero_lt_two;
                have hderiv :
                    deriv (fun θ => (2 * Real.cos ((n : ℝ) * θ)) ^ ((1 : ℝ) / n)) θ =
                      (1 / n : ℝ) * (2 * Real.cos ((n : ℝ) * θ)) ^
                        ((1 : ℝ) / n - 1) * (-2 * n * Real.sin ((n : ℝ) * θ)) := by
                  have hf : HasDerivAt (fun x : ℝ => Real.cos (x * (n : ℝ)) * 2)
                      ((-Real.sin (θ * (n : ℝ)) * (n : ℝ)) * 2) θ := by
                    simpa using
                      ((Real.hasDerivAt_cos (θ * (n : ℝ))).comp θ
                        ((hasDerivAt_id θ).mul_const (n : ℝ)) |>.mul_const 2);
                  have hg : HasDerivAt (fun _ : ℝ => ((n : ℝ)⁻¹)) 0 θ :=
                    hasDerivAt_const θ _;
                  have h := (HasDerivAt.rpow hf hg hcos_pos).deriv;
                  rw [show (fun θ : ℝ => (2 * Real.cos ((n : ℝ) * θ)) ^ ((1 : ℝ) / n)) =
                      (fun θ : ℝ => (Real.cos (θ * (n : ℝ)) * 2) ^ ((n : ℝ)⁻¹)) by
                    funext x;
                    ring_nf];
                  rw [h];
                  ring_nf;
                simpa [mul_comm, add_comm, add_left_comm, add_assoc] using hderiv;
            · exact Continuous.continuousOn ( by continuity );
          · exact ContinuousOn.mul ( ContinuousOn.mul ( Complex.continuous_ofReal.comp_continuousOn <| ContinuousOn.rpow ( continuousOn_const.mul <| Real.continuous_cos.comp_continuousOn <| continuousOn_const.mul continuousOn_id ) continuousOn_const <| by intro x hx; exact Or.inr <| by positivity ) <| Complex.continuous_exp.comp_continuousOn <| ContinuousOn.mul ( Complex.continuous_ofReal.comp_continuousOn <| continuousOn_id ) continuousOn_const ) continuousOn_const;
        refine h_cont_deriv.congr ?_;
        intro θ hθ;
        refine Filter.EventuallyEq.deriv_eq ?_;
        filter_upwards [ Ioo_mem_nhds hθ.1 hθ.2 ] with x hx using by rw [ show lemniscatePetalCurve n x = ( ( 2 * Real.cos ( n * x ) ) ^ ( 1 / n : ℝ ) : ℝ ) * Complex.exp ( x * Complex.I ) from by rw [ lemniscatePetalCurve ] ; rw [ max_eq_right ( mul_nonneg zero_le_two ( Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, hx.1, hx.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, hx.1, hx.2, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ⟩ ) ) ] ] ;

/-- On any truncated closed subinterval [a+ε, b-ε] with ε > 0,
    the derivative is continuous on the closed subinterval.
    This follows from continuity on the open interval and the truncated
    subinterval being contained in the open interval. -/
lemma petal_deriv_continuousOn_truncated (n : ℕ) (hn : n ≥ 1)
    (ε : ℝ) (hε : 0 < ε) (_hε_small : ε < Real.pi / (2 * ↑n)) :
    ContinuousOn (deriv (lemniscatePetalCurve n))
      (Icc (-(Real.pi / (2 * ↑n)) + ε) (Real.pi / (2 * ↑n) - ε)) := by
  apply ContinuousOn.mono (petal_deriv_continuousOn_interior n hn)
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The norm of the derivative is also continuous on truncated subintervals. -/
lemma petal_deriv_norm_continuousOn_truncated (n : ℕ) (hn : n ≥ 1)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < Real.pi / (2 * ↑n)) :
    ContinuousOn (fun t => ‖deriv (lemniscatePetalCurve n) t‖)
      (Icc (-(Real.pi / (2 * ↑n)) + ε) (Real.pi / (2 * ↑n) - ε)) :=
  ContinuousOn.norm (petal_deriv_continuousOn_truncated n hn ε hε hε_small)

/-
The integral of ‖γ'‖ is integrable on the full interval. This follows from
    lemniscate_arc_integral_eq (the integral equals lemniscateLength n, which is finite).
-/
lemma petal_integrable (n : ℕ) (hn : n ≥ 1) :
    IntervalIntegrable (fun t => ‖deriv (lemniscatePetalCurve n) t‖)
      MeasureTheory.volume
      (-(Real.pi / (2 * ↑n))) (Real.pi / (2 * ↑n)) := by
        apply Classical.byContradiction
        intro h_not_integrable;
        have h_integrable : ∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) t‖ = lemniscateLength n := by
          exact lemniscate_arc_integral_eq n hn
        rw [ intervalIntegral.integral_undef h_not_integrable ] at h_integrable;
        exact absurd h_integrable <| ne_of_lt <| mul_pos ( by positivity ) <| div_pos ( mul_pos ( Real.Gamma_pos_of_pos <| by positivity ) ( Real.Gamma_pos_of_pos <| by positivity ) ) <| Real.Gamma_pos_of_pos <| by positivity;

/-! ## Lower bound: ENNReal.ofReal(∫ ‖γ'‖) ≤ μH[1](γ '' Icc a b) -/

/-
For each truncated subinterval, the integral is a lower bound for the
    Hausdorff measure of the petal image. Uses integral_le_eVariationOn and
    eVariationOn_le_hausdorffMeasure_injective on the subinterval.
-/
lemma hausdorffMeasure_petal_ge_truncated (n : ℕ) (hn : n ≥ 1)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < Real.pi / (2 * ↑n)) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    ENNReal.ofReal (∫ t in (a + ε)..(b - ε), ‖deriv (lemniscatePetalCurve n) t‖) ≤
      μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc a b) := by
        let a := -(Real.pi / (2 * ↑n))
        let b := Real.pi / (2 * ↑n)
        have := @Erdos1044.eVariationOn_le_hausdorffMeasure_injective;
        refine le_trans ?_ ( this ?_ ?_ ?_ );
        · refine le_trans
            (b := eVariationOn (lemniscatePetalCurve n) (Icc (a + ε) (b - ε))) ?_
            ( eVariationOn.mono (lemniscatePetalCurve n) ?_ );
          · exact integral_le_eVariationOn (by linarith)
              (ContinuousOn.mono (petal_continuousOn n hn)
                (Set.Icc_subset_Icc (by linarith) (by linarith)))
              (fun t ht => petal_differentiableAt n hn t
                ⟨by linarith [ht.1], by linarith [ht.2]⟩)
              (petal_deriv_continuousOn_truncated n hn ε hε hε_small)
          · exact Set.Icc_subset_Icc
              ( by dsimp [a, b]; nlinarith [hε] )
              ( by dsimp [a, b]; nlinarith [hε] );
        · grind;
        · exact petal_continuousOn n hn
        · exact petal_injOn n hn

/-
The integral on the full interval equals the sup of integrals on truncated intervals.
-/
lemma petal_integral_limit (n : ℕ) (hn : n ≥ 1) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    ENNReal.ofReal (∫ t in a..b, ‖deriv (lemniscatePetalCurve n) t‖) ≤
      μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc a b) := by
        refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_;
        -- Choose $\varepsilon$ small enough such that the integral over $[a + \varepsilon, b - \varepsilon]$ is close to the integral over $[a, b]$.
        obtain ⟨ε, hε_pos, hε_small⟩ : ∃ ε > 0, ε < Real.pi / (2 * n) ∧ ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)) + ε)..(Real.pi / (2 * n) - ε), ‖deriv (lemniscatePetalCurve n) t‖) > r := by
          have h_cont : Filter.Tendsto (fun ε => ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)) + ε)..(Real.pi / (2 * n) - ε), ‖deriv (lemniscatePetalCurve n) t‖)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) t‖))) := by
            refine ENNReal.tendsto_ofReal ?_;
            have h_integrable : IntervalIntegrable (fun t => ‖deriv (lemniscatePetalCurve n) t‖) MeasureTheory.volume (-(Real.pi / (2 * n))) (Real.pi / (2 * n)) := by
              contrapose! hr;
              rw [ intervalIntegral.integral_undef hr ] ; norm_num;
            have h_cont : ContinuousOn (fun ε => ∫ t in (-(Real.pi / (2 * n)) + ε)..(Real.pi / (2 * n) - ε), ‖deriv (lemniscatePetalCurve n) t‖) (Set.Icc 0 (Real.pi / (2 * n))) := by
              have h_cont : ContinuousOn (fun ε => ∫ t in (-(Real.pi / (2 * n)))..ε, ‖deriv (lemniscatePetalCurve n) t‖) (Set.Icc (-(Real.pi / (2 * n))) (Real.pi / (2 * n))) := by
                intro ε hε; apply_rules [ intervalIntegral.continuousWithinAt_primitive, h_integrable ] ; aesop;
                cases max_cases ( - ( Real.pi / ( 2 * n ) ) ) ( Real.pi / ( 2 * n ) ) <;> aesop;
              have h_cont : ContinuousOn (fun ε => (∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n) - ε), ‖deriv (lemniscatePetalCurve n) t‖) - (∫ t in (-(Real.pi / (2 * n)))..(-(Real.pi / (2 * n)) + ε), ‖deriv (lemniscatePetalCurve n) t‖)) (Set.Icc 0 (Real.pi / (2 * n))) := by
                exact ContinuousOn.sub ( h_cont.comp ( continuousOn_const.sub continuousOn_id ) fun x hx => ⟨ by linarith [ hx.1, hx.2, Real.pi_pos, show ( Real.pi : ℝ ) / ( 2 * n ) ≥ 0 by positivity ], by linarith [ hx.1, hx.2, Real.pi_pos, show ( Real.pi : ℝ ) / ( 2 * n ) ≥ 0 by positivity ] ⟩ ) ( h_cont.comp ( continuousOn_const.add continuousOn_id ) fun x hx => ⟨ by linarith [ hx.1, hx.2, Real.pi_pos, show ( Real.pi : ℝ ) / ( 2 * n ) ≥ 0 by positivity ], by linarith [ hx.1, hx.2, Real.pi_pos, show ( Real.pi : ℝ ) / ( 2 * n ) ≥ 0 by positivity ] ⟩ );
              refine h_cont.congr fun ε hε => ?_;
              rw [ eq_sub_iff_add_eq', intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ h_integrable.mono_set, Set.Icc_subset_Icc ] <;> norm_num [ hε.1, hε.2 ];
              · exact Or.inr ( by linarith [ hε.2, show 0 ≤ Real.pi / ( 2 * n ) by positivity ] );
              · exact ⟨ by cases min_cases ( - ( Real.pi / ( 2 * n ) ) ) ( Real.pi / ( 2 * n ) ) <;> linarith [ hε.1, hε.2 ], Or.inl <| by cases min_cases ( - ( Real.pi / ( 2 * n ) ) ) ( Real.pi / ( 2 * n ) ) <;> linarith [ hε.1, hε.2 ] ⟩;
              · exact Or.inr ( by linarith [ hε.1, hε.2 ] );
            have := h_cont 0 ( by norm_num; positivity );
            convert this.tendsto.mono_left _ using 2 <;> norm_num;
            rw [ nhdsWithin_le_iff ];
            exact mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨ Real.pi / ( 2 * n ), by norm_num; positivity, fun x hx => ⟨ hx.1.le, hx.2.le ⟩ ⟩;
          have := h_cont.eventually ( lt_mem_nhds hr ) ; have := this.and ( Ioo_mem_nhdsGT <| show 0 < Real.pi / ( 2 * n ) by positivity ) ; obtain ⟨ ε, hε₁, hε₂ ⟩ := this.exists ; exact ⟨ ε, hε₂.1, hε₂.2, hε₁ ⟩ ;
        exact hε_small.2.le.trans ( hausdorffMeasure_petal_ge_truncated n hn ε hε_pos hε_small.1 )

/-! ## Upper bound: μH[1](γ '' Icc a b) ≤ ENNReal.ofReal(∫ ‖γ'‖) -/

/-
The Hausdorff measure of the petal image on a truncated interval is bounded
    by the integral of the derivative norm on the full interval.
-/
lemma hausdorffMeasure_petal_le_truncated (n : ℕ) (hn : n ≥ 1)
    (ε : ℝ) (hε : 0 < ε) (hε_small : ε < Real.pi / (2 * ↑n)) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc (a + ε) (b - ε)) ≤
      ENNReal.ofReal (∫ t in a..b, ‖deriv (lemniscatePetalCurve n) t‖) := by
        refine le_trans ( hausdorffMeasure_curve_le_integral ?_ ?_ ?_ ?_ ) ?_;
        · linarith;
        · refine Continuous.continuousOn ?_;
          refine Continuous.mul ?_ ?_;
          · exact Complex.continuous_ofReal.comp <| Continuous.rpow ( continuous_const.max <| continuous_const.mul <| Real.continuous_cos.comp <| by continuity ) continuous_const <| by continuity;
          · continuity;
        · exact fun t ht => petal_differentiableAt n hn t ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩;
        · exact petal_deriv_norm_continuousOn_truncated n hn ε hε hε_small
        · apply_rules [ ENNReal.ofReal_le_ofReal, intervalIntegral.integral_mono_interval ];
          · linarith;
          · linarith;
          · linarith;
          · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · exact petal_integrable n hn

/-
The petal image on the closed interval differs from the image on the open
    interval by at most a single point {0}, which has μH[1]-measure 0.
-/
lemma hausdorffMeasure_petal_Icc_eq_Ioo (n : ℕ) (hn : n ≥ 1) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc a b) =
      μH[(1 : ℝ)] (lemniscatePetalCurve n '' Ioo a b) := by
        refine le_antisymm ?_ ?_;
        · have h_image_eq : lemniscatePetalCurve n '' Icc (-(Real.pi / (2 * n))) (Real.pi / (2 * n)) ⊆ lemniscatePetalCurve n '' Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n)) ∪ {0} := by
            rintro _ ⟨ x, hx, rfl ⟩;
            by_cases hx' : x = -(Real.pi / (2 * n)) ∨ x = Real.pi / (2 * n);
            · cases hx' <;> simp +decide [ *, lemniscatePetalCurve ];
              · ring_nf; norm_num [ mul_div, mul_comm, show n ≠ 0 by linarith ];
              · ring_nf; norm_num [ mul_div, mul_comm, show n ≠ 0 by linarith ];
            · exact Or.inl ⟨ x, ⟨ lt_of_le_of_ne hx.1 ( by tauto ), lt_of_le_of_ne hx.2 ( by tauto ) ⟩, rfl ⟩;
          have h_measure_zero : μH[1] ({0} : Set ℂ) = 0 := by
            simp +decide [ MeasureTheory.Measure.hausdorffMeasure_apply ];
            intro ε hε; rw [ @ciInf_eq_of_forall_ge_of_forall_gt_exists_lt ];
            · exact fun _ => zero_le _;
            · intro w hw; use fun _ => { 0 } ; aesop;
          exact le_trans ( MeasureTheory.measure_mono h_image_eq ) ( MeasureTheory.measure_union_le _ _ ) |> le_trans <| by aesop;
        · exact MeasureTheory.measure_mono ( Set.image_mono ( Set.Ioo_subset_Icc_self ) )

/-
The image of the open interval is the increasing union of images of
    truncated closed subintervals. By measure continuity from below,
    the μH[1] measure of the union equals the sup.
-/
lemma hausdorffMeasure_petal_le (n : ℕ) (hn : n ≥ 1) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc a b) ≤
      ENNReal.ofReal (∫ t in a..b, ‖deriv (lemniscatePetalCurve n) t‖) := by
        -- By the continuity of the integral, we can bound the integral over the closed interval by the integral over the open interval.
        have h_integral_bound : ∀ ε > 0, ε < Real.pi / (2 * n) → μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc (-(Real.pi / (2 * n)) + ε) (Real.pi / (2 * n) - ε)) ≤ ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) t‖) := by
          exact fun ε a a_1 ↦ hausdorffMeasure_petal_le_truncated n hn ε a a_1
        have h_integral_bound : μH[(1 : ℝ)] (lemniscatePetalCurve n '' Set.Ioo (-(Real.pi / (2 * n))) (Real.pi / (2 * n))) ≤ ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) t‖) := by
          have h_integral_bound : μH[(1 : ℝ)] (⋃ k : ℕ, lemniscatePetalCurve n '' Set.Icc (-(Real.pi / (2 * n)) + (Real.pi / (2 * n)) / (k + 2)) (Real.pi / (2 * n) - (Real.pi / (2 * n)) / (k + 2))) ≤ ENNReal.ofReal (∫ t in (-(Real.pi / (2 * n)))..(Real.pi / (2 * n)), ‖deriv (lemniscatePetalCurve n) t‖) := by
            refine le_of_tendsto_of_tendsto' ( MeasureTheory.tendsto_measure_iUnion_atTop ?_ ) ( tendsto_const_nhds ) ?_;
            · intro k l hkl;
              refine Set.image_mono ?_;
              exact Set.Icc_subset_Icc ( by gcongr ) ( by gcongr );
            · intro k; specialize h_integral_bound ( Real.pi / ( 2 * n ) / ( k + 2 ) ) ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> nlinarith [ Real.pi_pos, show ( n : ℝ ) ≥ 1 by norm_cast, mul_div_cancel₀ ( Real.pi : ℝ ) ( by positivity : ( 2 * n : ℝ ) ≠ 0 ) ] ) ; aesop;
          refine le_trans ?_ h_integral_bound;
          refine MeasureTheory.measure_mono ?_;
          intro x hx;
          obtain ⟨ t, ht, rfl ⟩ := hx;
          simp +zetaDelta at *;
          -- Choose $i$ such that $\frac{\pi}{2n(i+2)} < \min(t + \frac{\pi}{2n}, \frac{\pi}{2n} - t)$.
          obtain ⟨i, hi⟩ : ∃ i : ℕ, Real.pi / (2 * n) / (i + 2) < min (t + Real.pi / (2 * n)) (Real.pi / (2 * n) - t) := by
            exact ⟨ ⌊ ( Real.pi / ( 2 * n ) ) / ( Min.min ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) ) ⌋₊, by rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( ( Real.pi / ( 2 * n ) ) / ( Min.min ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) ) ), show 0 < Min.min ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) from lt_min ( by linarith ) ( by linarith ), mul_div_cancel₀ ( Real.pi / ( 2 * n ) ) ( ne_of_gt ( lt_min ( by linarith ) ( by linarith ) : 0 < Min.min ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) ) ) ] ⟩;
          exact ⟨ i, t, ⟨ by linarith [ min_le_left ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) ], by linarith [ min_le_right ( t + Real.pi / ( 2 * n ) ) ( Real.pi / ( 2 * n ) - t ) ] ⟩, rfl ⟩;
        convert h_integral_bound using 1;
        exact hausdorffMeasure_petal_Icc_eq_Ioo n hn

/-! ## Main result -/

/-- The Hausdorff 1-measure of the petal curve image equals the integral of the
    derivative norm, which equals lemniscateLength n. -/
theorem hausdorffMeasure_petal_eq (n : ℕ) (hn : n ≥ 1) :
    let a := -(Real.pi / (2 * ↑n))
    let b := Real.pi / (2 * ↑n)
    μH[(1 : ℝ)] (lemniscatePetalCurve n '' Icc a b) =
      ENNReal.ofReal (lemniscateLength n) := by
  simp only
  rw [← lemniscate_arc_integral_eq n hn]
  exact le_antisymm (hausdorffMeasure_petal_le n hn) (petal_integral_limit n hn)

end Erdos1044


/-! ### From RotationalSymmetry.lean -/

/-
  Rotational symmetry of OmegaSet(z^n - 1).
  Key structural result: multiplication by a primitive n-th root of unity
  is an isometry that permutes the connected components, hence all
  components have equal boundary length and LambdaFn equals the boundary
  length of any single component.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Multiplication by unit complex number is an isometry -/

lemma modelPoly_eval_rotation (n : ℕ) (ω : ℂ) (hω : ω ^ n = 1) (z : ℂ) :
    ‖Polynomial.eval (ω * z) (modelPoly n)‖ = ‖Polynomial.eval z (modelPoly n)‖ := by
  simp [modelPoly, mul_pow, hω]

/-- The OmegaSet of z^n - 1 is invariant under multiplication by an n-th root of unity. -/
lemma omegaSet_modelPoly_rotation (n : ℕ) (ω : ℂ) (hω : ω ^ n = 1) (hω_ne : ω ≠ 0) :
    (fun z => ω * z) '' OmegaSet (modelPoly n) = OmegaSet (modelPoly n) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    change ‖Polynomial.eval (ω * z) (modelPoly n)‖ < 1
    rw [modelPoly_eval_rotation n ω hω]
    exact hz
  · intro hw
    refine ⟨ω⁻¹ * w, ?_, by field_simp⟩
    change ‖Polynomial.eval (ω⁻¹ * w) (modelPoly n)‖ < 1
    have : (ω⁻¹) ^ n = 1 := by rw [inv_pow, hω, inv_one]
    rw [modelPoly_eval_rotation n ω⁻¹ this]
    exact hw

/-
Rotation by an n-th root of unity maps connected components of OmegaSet(z^n-1)
    to connected components.
-/
lemma connectedComponent_rotation (n : ℕ) (ω : ℂ) (hω : ω ^ n = 1) (hω_norm : ‖ω‖ = 1)
    (z : ℂ) (hz : z ∈ OmegaSet (modelPoly n)) :
    (fun w => ω * w) '' connectedComponentIn (OmegaSet (modelPoly n)) z =
      connectedComponentIn (OmegaSet (modelPoly n)) (ω * z) := by
  -- The map φ(w) = ω * w is a homeomorphism of ℂ (continuous bijection with continuous inverse w → ω⁻¹ * w, since ω ≠ 0 as |ω| = 1). It maps OmegaSet(z^n-1) to itself (by omegaSet_modelPoly_rotation). Therefore it maps connected components to connected components.
  have h_homeomorphism : Continuous (fun w : ℂ => ω * w) ∧ Continuous (fun w : ℂ => ω⁻¹ * w) ∧ Function.Bijective (fun w : ℂ => ω * w) := by
    exact ⟨ continuous_const.mul continuous_id', continuous_const.mul continuous_id', ⟨ mul_right_injective₀ <| by aesop_cat, mul_left_surjective₀ <| by aesop_cat ⟩ ⟩;
  refine Set.Subset.antisymm ?_ ?_;
  · apply_rules [ IsPreconnected.subset_connectedComponentIn ];
    · exact isPreconnected_connectedComponentIn.image _ h_homeomorphism.1.continuousOn;
    · exact ⟨ z, mem_connectedComponentIn ( by aesop ), rfl ⟩;
    · intro w hw;
      obtain ⟨ x, hx, rfl ⟩ := hw;
      exact omegaSet_modelPoly_rotation n ω hω ( by aesop ) ▸ Set.mem_image_of_mem _ ( connectedComponentIn_subset _ _ hx );
  · intro w hw;
    have h_image : (fun w => ω⁻¹ * w) '' connectedComponentIn (OmegaSet (modelPoly n)) (ω * z) ⊆ connectedComponentIn (OmegaSet (modelPoly n)) z := by
      apply_rules [ IsPreconnected.subset_connectedComponentIn ];
      · exact isPreconnected_connectedComponentIn.image _ h_homeomorphism.2.1.continuousOn;
      · use ω * z; simp;
        exact ⟨ mem_connectedComponentIn ( by simpa [ hω_norm ] using omegaSet_modelPoly_rotation n ω hω ( by aesop ) ▸ Set.mem_image_of_mem _ hz ), by rw [ ← mul_assoc, inv_mul_cancel₀ ( by aesop ), one_mul ] ⟩;
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := hx;
        have h_image : y ∈ OmegaSet (modelPoly n) := by
          exact connectedComponentIn_subset _ _ hy;
        convert omegaSet_modelPoly_rotation n ω⁻¹ _ _ |> fun h => h.subset ⟨ y, h_image, rfl ⟩ using 1 <;> simp +decide [ hω ];
        aesop;
    exact ⟨ ω⁻¹ * w, h_image ⟨ w, hw, rfl ⟩, by simp +decide [ show ω ≠ 0 from by rintro rfl; norm_num at hω_norm ] ⟩

/-
Frontier commutes with multiplication by a nonzero complex number (which is a homeomorphism).
-/
lemma frontier_mul_image (ω : ℂ) (hω_ne : ω ≠ 0) (S : Set ℂ) :
    frontier ((fun w => ω * w) '' S) = (fun w => ω * w) '' frontier S := by
  have h_homeo : IsHomeomorph (fun w => ω * w) := by
    constructor;
    · exact continuous_const.mul continuous_id;
    · exact fun s hs => by simpa [ hω_ne ] using hs.smul₀ hω_ne;
    · exact ⟨ mul_right_injective₀ hω_ne, mul_left_surjective₀ hω_ne ⟩;
  have h_frontier_comm : ∀ (f : ℂ ≃ₜ ℂ) (S : Set ℂ), frontier (f '' S) = f '' frontier S := by
    exact fun f S ↦ Eq.symm (Homeomorph.image_frontier f S)
  grind +suggestions

/-- The boundary of each connected component of OmegaSet(z^n-1) has the same
    Hausdorff 1-measure, thanks to the rotational isometry. -/
lemma componentBoundaryLength_rotation (n : ℕ) (ω : ℂ)
    (hω : ω ^ n = 1) (hω_norm : ‖ω‖ = 1)
    (z : ℂ) (hz : z ∈ OmegaSet (modelPoly n)) :
    componentBoundaryLength (modelPoly n) z =
      componentBoundaryLength (modelPoly n) (ω * z) := by
  unfold componentBoundaryLength
  rw [← connectedComponent_rotation n ω hω hω_norm z hz]
  have hω_ne : ω ≠ 0 := by intro h; simp [h, norm_zero] at hω_norm
  rw [frontier_mul_image ω hω_ne]
  exact ((isometry_mul_unit ω hω_norm).hausdorffMeasure_image (Or.inl one_pos.le) _).symm

/-
All connected components of OmegaSet(z^n-1) have the same boundary length.
-/
lemma modelPoly_uniform_boundary_length (n : ℕ) (hn : n ≥ 1)
    (z w : ℂ) (hz : z ∈ OmegaSet (modelPoly n)) (hw : w ∈ OmegaSet (modelPoly n)) :
    componentBoundaryLength (modelPoly n) z = componentBoundaryLength (modelPoly n) w := by
  -- Let $\omega = e^{2\pi i/n}$. Then $\omega^n = 1$ and $|\omega| = 1$.
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with h_ω_def;
  -- For any $z \in \Omega(z^n - 1)$, there exists $k \in \{0, 1, ..., n-1\}$ such that $z$ is in the same connected component as $\omega^k$.
  have h_component : ∀ z ∈ OmegaSet (modelPoly n), ∃ k : ℕ, k < n ∧ z ∈ connectedComponentIn (OmegaSet (modelPoly n)) (ω ^ k) := by
    -- By definition of $OmegaSet$, if $z \in OmegaSet (modelPoly n)$, then $|z^n - 1| < 1$.
    intro z hz
    have h_abs : ‖z^n - 1‖ < 1 := by
      unfold OmegaSet modelPoly at hz; aesop;
    -- Since $|z^n - 1| < 1$, we have $z^n = 1 + w$ for some $w$ with $|w| < 1$.
    obtain ⟨w, hw⟩ : ∃ w : ℂ, z^n = 1 + w ∧ ‖w‖ < 1 := by
      exact ⟨ z ^ n - 1, by ring, h_abs ⟩;
    -- Since $|w| < 1$, we can write $z = \omega^k (1 + v)^{1/n}$ for some $k \in \{0, 1, ..., n-1\}$ and $v$ with $|v| < 1$.
    obtain ⟨k, hk⟩ : ∃ k : ℕ, k < n ∧ ∃ v : ℂ, z = ω^k * (1 + v)^(1/n : ℂ) ∧ ‖v‖ < 1 := by
      -- Since $|w| < 1$, we can write $z = \omega^k (1 + v)^{1/n}$ for some $k \in \{0, 1, ..., n-1\}$ and $v$ with $|v| < 1$. Use this fact.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, k < n ∧ ∃ v : ℂ, z = ω^k * (1 + w)^(1/n : ℂ) := by
        -- Since $|w| < 1$, we can write $z = \omega^k (1 + w)^{1/n}$ for some $k \in \{0, 1, ..., n-1\}$.
        have h_root : ∃ k : ℕ, k < n ∧ z / (1 + w)^(1/n : ℂ) = ω^k := by
          have h_root_exists : (z / (1 + w)^(1/n : ℂ))^n = 1 := by
            rw [ div_pow, ← Complex.cpow_nat_mul ] ; norm_num [ hw.1, show n ≠ 0 by linarith ];
            exact fun h => by rw [ show w = -1 by linear_combination' h ] at hw; norm_num at hw;
          -- Since $(z / (1 + w)^(1/n))^n = 1$, we can write $z / (1 + w)^(1/n)$ as $e^{2\pi i k/n}$ for some integer $k$.
          obtain ⟨k, hk⟩ : ∃ k : ℤ, z / (1 + w)^(1/n : ℂ) = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
            have h_root_exists : ∃ θ : ℝ, z / (1 + w)^(1/n : ℂ) = Complex.exp (θ * Complex.I) := by
              have h_root_exists : ‖z / (1 + w)^(1/n : ℂ)‖ = 1 := by
                have := congr_arg Norm.norm h_root_exists ; norm_num at this;
                rw [ pow_eq_one_iff_of_nonneg ( by positivity ) ] at this <;> aesop;
              rw [ Complex.norm_eq_one_iff ] at h_root_exists ; tauto;
            obtain ⟨ θ, hθ ⟩ := h_root_exists; simp_all +decide [ ← Complex.exp_nat_mul ] ;
            rw [ Complex.exp_eq_one_iff ] at h_root_exists; obtain ⟨ k, hk ⟩ := h_root_exists; exact ⟨ k, congr_arg Complex.exp <| by rw [ eq_div_iff <| Nat.cast_ne_zero.mpr <| ne_bot_of_gt hn ] ; linear_combination' hk ⟩ ;
          -- Since $k$ is an integer, we can write $k = qn + r$ for some integer $q$ and $0 \leq r < n$.
          obtain ⟨q, r, hr⟩ : ∃ q : ℤ, ∃ r : ℕ, r < n ∧ k = q * n + r := by
            exact ⟨ k / n, Int.toNat ( k % n ), by linarith [ Int.emod_lt_of_pos k ( by positivity : 0 < ( n : ℤ ) ), Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ), Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ) ) ], by linarith [ Int.emod_add_mul_ediv k n, Int.toNat_of_nonneg ( Int.emod_nonneg k ( by positivity : ( n : ℤ ) ≠ 0 ) ) ] ⟩;
          use r;
          simp_all +decide [ ← Complex.exp_nat_mul ];
          exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨ q, by ring_nf; norm_num [ show n ≠ 0 by linarith ] ⟩;
        obtain ⟨ k, hk₁, hk₂ ⟩ := h_root;
        by_cases h : ( 1 + w ) ^ ( 1 / ( n : ℂ ) ) = 0 <;> simp_all +decide [ div_eq_iff ];
        · exact ⟨ k, hk₁ ⟩;
        · exact ⟨ k, hk₁, Or.inl rfl ⟩;
      exact ⟨ k, hk.1, w, hk.2.choose_spec, hw.2 ⟩;
    -- Since $|v| < 1$, the path $t \mapsto \omega^k (1 + tv)^{1/n}$ for $t \in [0, 1]$ is contained in $\Omega(z^n - 1)$.
    obtain ⟨v, hv⟩ := hk.right
    have h_path : ∀ t ∈ Set.Icc (0 : ℝ) 1, ω^k * (1 + t * v)^(1/n : ℂ) ∈ OmegaSet (modelPoly n) := by
      intro t ht
      have h_path : ‖(ω^k * (1 + t * v)^(1/n : ℂ))^n - 1‖ < 1 := by
        rw [ mul_pow, ← Complex.cpow_nat_mul ] ; norm_num [ show n ≠ 0 by linarith ];
        rw [ ← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm ];
        rw [ mul_div_cancel₀ ] <;> norm_num [ show n ≠ 0 by linarith ];
        exact lt_of_le_of_lt ( mul_le_of_le_one_left ( norm_nonneg _ ) ( abs_le.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ) ) hv.2;
      unfold OmegaSet modelPoly; aesop;
    -- Since the path $t \mapsto \omega^k (1 + tv)^{1/n}$ is contained in $\Omega(z^n - 1)$, it follows that $z$ is in the same connected component as $\omega^k$.
    have h_connected : IsConnected (Set.image (fun t : ℝ => ω^k * (1 + t * v)^(1/n : ℂ)) (Set.Icc (0 : ℝ) 1)) := by
      apply_rules [ IsConnected.image, isConnected_Icc ];
      · norm_num;
      · refine ContinuousOn.mul continuousOn_const ?_;
        refine ContinuousOn.cpow ?_ ?_ ?_;
        · fun_prop;
        · exact continuousOn_const;
        · norm_num [ Complex.ext_iff, slitPlane ];
          intro a ha₁ ha₂; contrapose! hv; simp_all +decide [ Complex.normSq, Complex.norm_def ];
          by_cases ha₃ : a = 0 <;> simp_all +decide;
          · linarith;
          · exact fun _ => by nlinarith [ mul_self_pos.mpr ha₃, mul_le_mul_of_nonneg_left ha₂ ha₁ ] ;
    have h_connected : Set.image (fun t : ℝ => ω^k * (1 + t * v)^(1/n : ℂ)) (Set.Icc (0 : ℝ) 1) ⊆ connectedComponentIn (OmegaSet (modelPoly n)) (ω^k) := by
      apply_rules [ IsPreconnected.subset_connectedComponentIn ];
      · exact h_connected.isPreconnected;
      · exact ⟨ 0, by norm_num, by norm_num ⟩;
      · exact Set.image_subset_iff.mpr h_path;
    exact ⟨ k, hk.1, hv.1.symm ▸ h_connected ⟨ 1, by norm_num, by norm_num ⟩ ⟩;
  -- By the properties of the connected components and the rotational symmetry, we have:
  have h_symm : ∀ k : ℕ, k < n → componentBoundaryLength (modelPoly n) (ω ^ k) = componentBoundaryLength (modelPoly n) 1 := by
    intro k hk_lt_n
    have h_symm_step : ∀ m : ℕ, m < n → componentBoundaryLength (modelPoly n) (ω ^ m) = componentBoundaryLength (modelPoly n) (ω ^ (m + 1)) := by
      intro m hm_lt_n
      have h_symm_step : componentBoundaryLength (modelPoly n) (ω ^ m) = componentBoundaryLength (modelPoly n) (ω * (ω ^ m)) := by
        apply componentBoundaryLength_rotation;
        · rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ] ; use 1 ; ring_nf ; norm_num [ show n ≠ 0 by linarith ];
        · norm_num [ ω, Complex.norm_exp ];
        · simp_all +decide [ modelPoly, OmegaSet ];
          rw [ ← pow_mul, Nat.mul_comm, pow_mul, ← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ ] <;> aesop;
      rw [ h_symm_step, pow_succ' ];
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      rw [ ← h_symm_step k ( Nat.lt_of_succ_lt hk_lt_n ), ih ( Nat.lt_of_succ_lt hk_lt_n ) ];
  -- By the properties of the connected components and the rotational symmetry, we have that for any $z \in \Omega(z^n - 1)$, $componentBoundaryLength (modelPoly n) z = componentBoundaryLength (modelPoly n) 1$.
  have h_eq : ∀ z ∈ OmegaSet (modelPoly n), componentBoundaryLength (modelPoly n) z = componentBoundaryLength (modelPoly n) 1 := by
    intro z hz
    obtain ⟨k, hk₁, hk₂⟩ := h_component z hz
    have h_eq : componentBoundaryLength (modelPoly n) z = componentBoundaryLength (modelPoly n) (ω ^ k) := by
      unfold componentBoundaryLength;
      rw [ connectedComponentIn_eq hk₂ ];
    rw [h_eq, h_symm k hk₁];
  rw [ h_eq z hz, h_eq w hw ]

/-- LambdaFn(z^n - 1) equals the boundary length of the component containing 1.
    Since all components have equal boundary length, the supremum equals this common value. -/
lemma lambdaFn_modelPoly_eq_single_component (n : ℕ) (hn : n ≥ 1) :
    LambdaFn (modelPoly n) = componentBoundaryLength (modelPoly n) 1 := by
  have h1 : (1 : ℂ) ∈ OmegaSet (modelPoly n) := by
    simp [OmegaSet, modelPoly]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun z hz => ?_
    rw [modelPoly_uniform_boundary_length n hn z 1 hz h1]
  · exact le_iSup₂_of_le 1 h1 le_rfl

/-- The arc-length formula for the boundary of the component of OmegaSet(z^n-1)
    containing 1. The boundary is a smooth lemniscate arc, and its Hausdorff
    1-measure equals lemniscateLength n = (2^{1/n}/n) · B(1/2, 1/(2n)).

    Decomposed into three sub-lemmas in ArcLength.lean:
    1. `frontier_component_one_eq_lemniscate_arc`: frontier = image of petal curve
    2. `hausdorffMeasure_curve_eq_integral`: μH[1](γ([a,b])) = ∫|γ'|
    3. `lemniscate_arc_integral_eq`: the integral = lemniscateLength n
    Plus verification of continuity/differentiability/injectivity hypotheses. -/
lemma component_boundary_length_eq_lemniscateLength (n : ℕ) (hn : n ≥ 1) :
    componentBoundaryLength (modelPoly n) 1 = ENNReal.ofReal (lemniscateLength n) := by
  unfold componentBoundaryLength
  rw [frontier_component_one_eq_lemniscate_arc n hn]
  exact hausdorffMeasure_petal_eq n hn

end Erdos1044


/-! ### From PommerenkeProof.lean -/

/-
  Helper lemmas for the proof of Pommerenke's component diameter bound.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Blaschke factor inequalities (proved) -/

lemma blaschke_norm_sq_le (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ^ 2 ≤ ‖1 - starRingEnd ℂ a * z‖ ^ 2 := by
      norm_num [ Complex.normSq, Complex.sq_norm ] at *
      norm_num [ Complex.normSq, Complex.norm_def ] at *
      rw [ Real.sqrt_lt' ] at ha <;> nlinarith

lemma blaschke_norm_le (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    ‖z - a‖ ≤ ‖1 - starRingEnd ℂ a * z‖ :=
  le_of_pow_le_pow_left₀ (by norm_num) (by positivity) (blaschke_norm_sq_le a z ha hz)

lemma blaschke_denom_ne_zero (a z : ℂ) (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    (1 : ℂ) - starRingEnd ℂ a * z ≠ 0 :=
  sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <|
    by norm_num; nlinarith [ norm_nonneg a, norm_nonneg z ]

lemma blaschke_prod_norm_le (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(S.map (fun a => (z - a) / (1 - starRingEnd ℂ a * z))).prod‖ ≤ 1 := by
      induction S using Multiset.induction <;> norm_num at *
      exact mul_le_one₀
        (div_le_one_of_le₀ (by simpa using blaschke_norm_le _ _ hS.1 hz) (norm_nonneg _))
        (div_nonneg (norm_nonneg _) (norm_nonneg _)) (by apply_assumption; tauto)

/-! ## Maximum modulus principle consequence (proved) -/

lemma holomorphic_constant_of_norm_bounds
    (U : Set ℂ) (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hU_bdd : Bornology.IsBounded U) (hU_ne : U.Nonempty)
    (Φ : ℂ → ℂ) (hΦ_diff : DifferentiableOn ℂ Φ U)
    (hΦ_cont : ContinuousOn Φ (closure U))
    (ha : ∀ z ∈ frontier U, 1 ≤ ‖Φ z‖)
    (hb : ∃ z₀ ∈ U, ‖Φ z₀‖ ≤ 1)
    (hc : ∀ z ∈ U, Φ z ≠ 0) :
    ∃ c, Set.EqOn Φ (Function.const ℂ c) U := by
      -- By the maximum modulus principle, since Φ is holomorphic on U and continuous on its closure, and attains a maximum of 1 at some point in U, Φ must be constant.
      have h_max_modulus : ∀ z ∈ U, ‖(Φ z)⁻¹‖ ≤ 1 := by
        -- Since Φ is holomorphic on U and continuous on its closure, 1/Φ is also holomorphic on U and continuous on its closure.
        have h_inv_diff : DifferentiableOn ℂ (fun z => (Φ z)⁻¹) U := by
          exact DifferentiableOn.inv hΦ_diff hc
        have h_inv_cont : ContinuousOn (fun z => (Φ z)⁻¹) (closure U) := by
          refine ContinuousOn.inv₀ hΦ_cont ?_;
          intro z hz;
          exact fun h => absurd ( ha z <| by rw [ frontier_eq_closure_inter_closure ] ; aesop ) ( by norm_num [ h ] );
        have := @Complex.exists_mem_frontier_isMaxOn_norm;
        specialize this hU_bdd hU_ne ⟨ h_inv_diff, h_inv_cont ⟩;
        obtain ⟨ z, hz₁, hz₂ ⟩ := this; exact fun w hw => le_trans ( hz₂ <| subset_closure hw ) <| by simpa [ norm_inv ] using inv_le_one_of_one_le₀ <| ha z hz₁;
      have h_const : ∀ z ∈ U, (Φ z)⁻¹ = (Φ hb.choose)⁻¹ := by
        apply_rules [ Complex.eqOn_of_isPreconnected_of_isMaxOn_norm ];
        · exact DifferentiableOn.inv hΦ_diff hc;
        · exact hb.choose_spec.1;
        · exact fun z hz => le_trans ( h_max_modulus z hz ) ( by simpa [ hb.choose_spec.2 ] using inv_anti₀ ( norm_pos_iff.mpr ( hc _ hb.choose_spec.1 ) ) hb.choose_spec.2 );
      exact ⟨ Φ hb.choose, fun z hz => inv_injective <| h_const z hz ⟩

/-! ## Auxiliary norm lemmas -/

lemma multiset_prod_norm_le_one (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ ≤ 1) :
    ‖S.prod‖ ≤ 1 := by
      induction S using Multiset.induction with
      | empty =>
        norm_num
      | cons a S ih =>
        simpa using mul_le_mul ( hS a ( Multiset.mem_cons_self _ _ ) )
          ( ih fun x hx => hS x ( Multiset.mem_cons_of_mem hx ) )
          ( by positivity )
          ( by positivity )

lemma blaschke_factorization (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ < 1)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (S.map (fun a => z - a)).prod =
    (S.map (fun a => (z - a) / (1 - starRingEnd ℂ a * z))).prod *
    (S.map (fun a => 1 - starRingEnd ℂ a * z)).prod := by
      rw [ ← Multiset.prod_map_mul ];
      exact congr_arg _ ( Multiset.map_congr rfl fun x hx => by rw [ div_mul_cancel₀ _ ( blaschke_denom_ne_zero x z ( hS x hx ) hz ) ] )

end Erdos1044


/-! ### From PommerenkeProof2.lean -/

/-
  Additional helper lemmas for pommerenke_component_diam.
-/

open Polynomial MeasureTheory Topology Set Metric Complex

noncomputable section

namespace Erdos1044

/-! ## Component contained in ball when diam ≤ 1 -/

lemma component_sub_ball_of_diam_le
    (U : Set ℂ) (hU_open : IsOpen U)
    (hU_bdd : Bornology.IsBounded U)
    (h0_in : (0 : ℂ) ∈ U)
    (h_le : Metric.diam U ≤ 1) :
    U ⊆ Metric.ball 0 1 := by
      -- Since $U$ is open and $0 \in U$,
      have hU_subset_closedBall : U ⊆ Metric.closedBall 0 1 := by
        intro z hz
        have h_dist_le_one : dist z 0 ≤ 1 := by
          refine le_trans ?_ h_le;
          apply_rules [ dist_le_diam_of_mem ]
        exact h_dist_le_one;
      have hU_subset_interior : U ⊆ interior (Metric.closedBall 0 1) := by
        exact (IsOpen.subset_interior_iff hU_open).mpr hU_subset_closedBall
      simpa [ interior_closedBall ] using hU_subset_interior

/-! ## Φ has no zeros in U₀ -/

/-
If S consists of elements with ‖·‖ < 1 and z ∈ ball(0,1),
    then (S.map (fun a => 1 - conj(a) * z)).prod ≠ 0.
-/
lemma blaschke_conjugate_prod_ne_zero
    (S : Multiset ℂ) (hS : ∀ a ∈ S, ‖a‖ < 1)
    (z : ℂ) (hz : ‖z‖ < 1) :
    (S.map (fun a => 1 - starRingEnd ℂ a * z)).prod ≠ 0 := by
      simp +zetaDelta at *;
      exact fun x hx => sub_ne_zero_of_ne <| ne_of_apply_ne Norm.norm <| by norm_num; nlinarith [ hS x hx, norm_nonneg x, norm_nonneg z ] ;

/-
If T consists of elements NOT in U₀, and z ∈ U₀,
    then (T.map (fun b => z - b)).prod ≠ 0.
-/
lemma sub_prod_ne_zero_of_not_mem
    (T : Multiset ℂ) (U₀ : Set ℂ)
    (hT : ∀ b ∈ T, b ∉ U₀) (z : ℂ) (hz : z ∈ U₀) :
    (T.map (fun b => z - b)).prod ≠ 0 := by
      simp_all +decide [ sub_eq_zero ];
      exact fun h => hT z h hz

/-! ## Φ is differentiable -/

lemma multiset_prod_sub_differentiable (T : Multiset ℂ) :
    Differentiable ℂ (fun z => (T.map (fun b => z - b)).prod) := by
      induction T using Multiset.induction <;> simp_all +decide [ sub_eq_add_neg ]

lemma multiset_prod_blaschke_differentiable (S : Multiset ℂ) :
    Differentiable ℂ (fun z => (S.map (fun a => (1 : ℂ) - starRingEnd ℂ a * z)).prod) := by
      induction S using Multiset.induction <;> simp_all +decide [ mul_comm ]

/-! ## Analytic continuation: constant on open → constant everywhere -/

/-
An entire function constant on a nonempty open set is constant everywhere.
-/
lemma entire_const_of_eqOn_open
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (U : Set ℂ) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (c : ℂ) (hc : Set.EqOn g (Function.const ℂ c) U) :
    ∀ z, g z = c := by
      intro z; exact (by
      have h_eq : AnalyticOnNhd ℂ g Set.univ := by
        exact analyticOnNhd_univ_iff_differentiable.mpr hg
      apply h_eq.eqOn_of_preconnected_of_eventuallyEq;
      exacts [ analyticOnNhd_const, isPreconnected_univ, trivial, Filter.eventually_of_mem ( hU_open.mem_nhds hU_ne.some_mem ) hc, trivial ])

/-! ## Φ constant → all roots zero or diam > 1 -/

/-
If all roots of a monic polynomial of degree ≥ 1 with roots in B̄(0,1) are at 0,
    then f = X^n and Ω(f) = B(0,1) which has diam = 2.
-/
lemma diam_gt_one_if_all_roots_zero
    (f : Polynomial ℂ) (hf : IsAdmissible f) (hdeg : f.natDegree ≥ 1)
    (hall : ∀ z, f.IsRoot z → z = 0) :
    1 < Metric.diam (connectedComponentIn (OmegaSet f) 0) := by
      -- By definition of `modelPoly`, $f(z) = X^n$.
      have hf_eq_modelPoly : ∃ n : ℕ, f = Polynomial.X ^ n := by
        have h_f_form : f = Polynomial.C (f.leadingCoeff) * (Polynomial.X - Polynomial.C 0) ^ f.natDegree := by
          have h_f_form : f = Polynomial.C (f.leadingCoeff) * Multiset.prod (Multiset.map (fun z => Polynomial.X - Polynomial.C z) (Polynomial.roots f)) := by
            convert Polynomial.Splits.eq_prod_roots _;
            exact IsAlgClosed.splits f
          rw [ h_f_form, show f.roots = Multiset.replicate f.natDegree 0 from ?_ ];
          · norm_num [ Polynomial.natDegree_mul', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_X_pow, Polynomial.leadingCoeff_C, show f ≠ 0 by rintro rfl; contradiction ];
          · refine Multiset.eq_replicate.mpr ⟨ ?_, ?_ ⟩;
            · replace h_f_form := congr_arg Polynomial.natDegree h_f_form; rw [ Polynomial.natDegree_mul' ] at h_f_form <;> norm_num at *;
              · linarith;
              · exact ⟨ by rintro rfl; contradiction, fun x hx hx' => Polynomial.X_sub_C_ne_zero x ⟩;
            · exact fun z hz => hall z <| Polynomial.isRoot_of_mem_roots hz;
        exact ⟨ f.natDegree, by simpa [ hf.1 ] using h_f_form ⟩;
      obtain ⟨ n, rfl ⟩ := hf_eq_modelPoly
      -- Since $f = X^n$, we have $\Omega(f) = \{z \in \mathbb{C} : \|z\|^n < 1\} = \{z \in \mathbb{C} : \|z\| < 1\} = B(0, 1)$.
      have h_omegaSet : OmegaSet (X ^ n) = Metric.ball 0 1 := by
        unfold OmegaSet;
        rcases n with ( _ | _ | n ) <;> norm_num at *;
        · norm_num [ Set.ext_iff, Metric.mem_ball ];
        · norm_num [ Set.ext_iff, pow_lt_one_iff_of_nonneg ];
      rw [ h_omegaSet ];
      -- The connected component of the ball at 0 is the ball itself.
      have h_connectedComponent : connectedComponentIn (Metric.ball (0 : ℂ) 1) 0 = Metric.ball (0 : ℂ) 1 := by
        apply_rules [ IsPreconnected.connectedComponentIn, convex_ball ];
        · exact convex_ball _ _ |> Convex.isPreconnected;
        · norm_num;
      rw [h_connectedComponent];
      refine lt_of_lt_of_le
        (show 1 < dist (3 / 4 : ℂ) (-3 / 4 : ℂ) by norm_num [dist_eq_norm])
        (Metric.dist_le_diam_of_mem (s := Metric.ball (0 : ℂ) 1)
          Metric.isBounded_ball
          (show (3 / 4 : ℂ) ∈ Metric.ball (0 : ℂ) 1 by norm_num [dist_eq_norm])
          (show (-3 / 4 : ℂ) ∈ Metric.ball (0 : ℂ) 1 by norm_num [dist_eq_norm]))

/-
If the Blaschke-modified function Φ is globally constant, then either
    all roots are 0 (giving diam = 2 > 1) or we have a contradiction.
-/
lemma phi_not_const_or_all_roots_zero
    (f : Polynomial ℂ) (hf : IsAdmissible f) (hdeg : f.natDegree ≥ 1)
    (S T : Multiset ℂ) (hST : f.roots = S + T)
    (hS_norm : ∀ a ∈ S, ‖a‖ < 1) (hT_norm : ∀ b ∈ T, ‖b‖ ≤ 1)
    (c : ℂ)
    (hc : ∀ z, (S.map (fun a => 1 - starRingEnd ℂ a * z)).prod *
               (T.map (fun b => z - b)).prod = c) :
    ∀ z, f.IsRoot z → z = 0 := by
      -- If $c = 0$, then $\Phi(0) = 0$, but $\Phi(0)$ is the product of terms, which can't be zero unless one of the terms is zero. However, since $0 \in U₀$, this leads to a contradiction.
      by_cases hc_zero : c = 0;
      · simp_all +decide [ Multiset.prod_eq_zero_iff, sub_eq_zero ];
        have hT_zero : ∀ z : ℂ, ‖z‖ < 1 → z ∈ T := by
          intro z hz; specialize hc z; rcases hc with ( ⟨ a, ha, ha' ⟩ | ha ) <;> simp_all +decide [ eq_comm ] ;
          replace ha' := congr_arg Norm.norm ha'; norm_num at ha'; nlinarith [ hS_norm a ha, norm_nonneg a, norm_nonneg z ] ;
        have hT_inf : Set.Infinite {z : ℂ | ‖z‖ < 1} := by
          refine Set.infinite_of_injective_forall_mem ( fun x y hxy => ?_ ) fun n : ℕ => show ( 1 / 2 : ℂ ) ^ ( n + 1 ) ∈ { z : ℂ | ‖z‖ < 1 } from ?_ <;> norm_num [ pow_succ' ] at *;
          · apply_fun Complex.normSq at hxy ; norm_num [ Complex.normSq_eq_norm_sq ] at hxy ; aesop;
          · exact lt_of_le_of_lt ( mul_le_of_le_one_right ( by norm_num ) ( pow_le_one₀ ( by norm_num ) ( by norm_num ) ) ) ( by norm_num );
        exact False.elim <| hT_inf <| Set.Finite.subset ( T.finite_toSet ) fun x hx => hT_zero x hx;
      · intro z hz_root
        have hz_in_ST : z ∈ S + T := by
          exact hST ▸ Polynomial.mem_roots ( show f ≠ 0 from by aesop_cat ) |>.2 hz_root
        obtain hz_in_S | hz_in_T : z ∈ S ∨ z ∈ T := by
          aesop
        by_cases hz_ne_zero : z ≠ 0
        generalize_proofs at *;
        · have := hc ( 1 / starRingEnd ℂ z ) ; simp_all +decide [ div_eq_mul_inv, mul_comm ] ;
          rw [ Multiset.prod_eq_zero ( Multiset.mem_map.mpr ⟨ z, hz_in_S, ?_ ⟩ ) ] at this <;> simp_all +decide [ mul_comm ];
        · exact Classical.not_not.mp hz_ne_zero;
        · contrapose! hc_zero; have := hc z; simp_all +decide  ;
          exact hc z ▸ mul_eq_zero_of_right _ ( Multiset.prod_eq_zero ( by aesop ) )

/-! ## Main theorem -/

theorem pommerenke_component_diam' (f : Polynomial ℂ) (hf : IsAdmissible f)
    (hdeg : f.natDegree ≥ 1)
    (hf0 : ‖f.eval 0‖ < 1) :
    1 < Metric.diam (connectedComponentIn (OmegaSet f) 0) := by
  by_contra h_le
  push Not at h_le
  have h0_mem : (0 : ℂ) ∈ OmegaSet f := by simpa [OmegaSet] using hf0
  set U₀ := connectedComponentIn (OmegaSet f) 0
  have hU₀_open : IsOpen U₀ := IsOpen.connectedComponentIn (omegaSet_isOpen f)
  have hU₀_conn : IsPreconnected U₀ := isPreconnected_connectedComponentIn
  have h0_in : (0 : ℂ) ∈ U₀ := mem_connectedComponentIn h0_mem
  have hU₀_bdd : Bornology.IsBounded U₀ :=
    (omegaSet_isBounded f hf.1 hdeg).subset (connectedComponentIn_subset _ _)
  have hU_sub : U₀ ⊆ Metric.ball 0 1 :=
    component_sub_ball_of_diam_le U₀ hU₀_open hU₀_bdd h0_in h_le
  classical
  have hf_ne : f ≠ 0 := Polynomial.Monic.ne_zero hf.1
  have hf_factor : f = (f.roots.map (fun a => X - C a)).prod := by
    have := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := f))
    simp [hf.1.leadingCoeff] at this; exact this.symm
  set S := f.roots.filter (fun a => a ∈ U₀)
  set T := f.roots.filter (fun a => a ∉ U₀)
  have hST : f.roots = S + T := (Multiset.filter_add_not _ _).symm
  have hS_norm : ∀ a ∈ S, ‖a‖ < 1 := by
    intro a ha; rw [Multiset.mem_filter] at ha
    have := hU_sub ha.2; simp [Metric.mem_ball, dist_eq_norm] at this; exact this
  have hT_norm : ∀ b ∈ T, ‖b‖ ≤ 1 := by
    intro b hb; rw [Multiset.mem_filter] at hb
    exact hf.2 b ((Polynomial.mem_roots hf_ne).mp hb.1)
  have hT_not_in : ∀ b ∈ T, b ∉ U₀ := by
    intro b hb; exact (Multiset.mem_filter.mp hb).2
  set Φ : ℂ → ℂ := fun z =>
    (S.map (fun a => 1 - starRingEnd ℂ a * z)).prod *
    (T.map (fun b => z - b)).prod
  -- ‖Φ(0)‖ ≤ 1
  have hΦ_zero_le : ‖Φ 0‖ ≤ 1 := by
    simp only [Φ, mul_zero, sub_zero]
    rw [norm_mul]
    have h1 : (S.map (fun _ => (1:ℂ))).prod = 1 := by simp
    rw [h1, norm_one, one_mul]
    calc
      ‖(T.map (fun b => (0 : ℂ) - b)).prod‖ = ‖T.prod‖ := by
        simp [Multiset.prod_map_neg]
      _ ≤ 1 := multiset_prod_norm_le_one T hT_norm
  -- ‖Φ(w)‖ ≥ 1 on frontier U₀
  have hΦ_frontier : ∀ w ∈ frontier U₀, 1 ≤ ‖Φ w‖ := by
    intro w hw
    have hw_norm : ‖w‖ ≤ 1 := by
      have := frontier_subset_closure hw
      rw [mem_closure_iff_seq_limit] at this
      obtain ⟨seq, hseq1, hseq2⟩ := this
      exact le_of_tendsto' (hseq2.norm) fun n =>
        le_of_lt (by simpa [dist_eq_norm] using hU_sub (hseq1 n))
    have hf_w : ‖f.eval w‖ = 1 :=
      frontier_component_sub_lemniscate f 0 h0_mem hw
    have hf_eval_w : f.eval w =
        (S.map (fun a => w - a)).prod * (T.map (fun b => w - b)).prod := by
      conv_lhs => rw [hf_factor]
      simp [Polynomial.eval_multiset_prod, hST, Multiset.map_add, Multiset.prod_add]
    have hB_le : ‖(S.map (fun a => (w - a) / (1 - starRingEnd ℂ a * w))).prod‖ ≤ 1 :=
      blaschke_prod_norm_le S hS_norm w hw_norm
    have hfact : (S.map (fun a => w - a)).prod =
        (S.map (fun a => (w - a) / (1 - starRingEnd ℂ a * w))).prod *
        (S.map (fun a => 1 - starRingEnd ℂ a * w)).prod :=
      blaschke_factorization S hS_norm w hw_norm
    -- f(w) = B(w) * Φ(w), |f(w)| = 1, |B(w)| ≤ 1, so |Φ(w)| ≥ 1
    -- Since f(w) = B(w) * Φ(w) and |f(w)| = |B(w)| * |Φ(w)| = 1 and |B(w)| ≤ 1:
    -- |Φ(w)| ≥ 1
    -- Substitute hfact into hf_eval_w to get f.eval w = B * Φ(w).
    have h_sub : f.eval w = (Multiset.map (fun a => (w - a) / (1 - starRingEnd ℂ a * w)) S).prod * Φ w := by
      rw [ hf_eval_w, hfact, mul_assoc ];
    rw [ h_sub, norm_mul ] at hf_w ; nlinarith [ norm_nonneg ( Φ w ) ]
  -- Φ has no zeros in U₀
  have hΦ_no_zeros : ∀ z ∈ U₀, Φ z ≠ 0 := by
    intro z hz
    change (S.map (fun a => 1 - starRingEnd ℂ a * z)).prod *
         (T.map (fun b => z - b)).prod ≠ 0
    have hz_lt : ‖z‖ < 1 := by simpa [dist_eq_norm] using hU_sub hz
    exact mul_ne_zero (blaschke_conjugate_prod_ne_zero S hS_norm z hz_lt)
      (sub_prod_ne_zero_of_not_mem T U₀ hT_not_in z hz)
  -- Φ is differentiable
  have hΦ_diff : Differentiable ℂ Φ :=
    (multiset_prod_blaschke_differentiable S).mul (multiset_prod_sub_differentiable T)
  -- Φ is constant on U₀
  have hΦ_const := holomorphic_constant_of_norm_bounds U₀ hU₀_open hU₀_conn
    hU₀_bdd ⟨0, h0_in⟩ Φ hΦ_diff.differentiableOn
    hΦ_diff.continuous.continuousOn
    hΦ_frontier ⟨0, h0_in, hΦ_zero_le⟩ hΦ_no_zeros
  obtain ⟨c, hc⟩ := hΦ_const
  -- Φ is globally constant
  have hΦ_global : ∀ z, Φ z = c :=
    entire_const_of_eqOn_open Φ hΦ_diff U₀ hU₀_open ⟨0, h0_in⟩ c hc
  -- All roots must be zero
  have hall_zero := phi_not_const_or_all_roots_zero f hf hdeg S T hST hS_norm hT_norm c hΦ_global
  -- But then f = X^n and diam = 2 > 1
  exact absurd h_le (not_le.mpr (by linarith [diam_gt_one_if_all_roots_zero f hf hdeg hall_zero]))

end Erdos1044


/-! ### From MainTheorem.lean -/

/-
  Main results from "On Erdős Problem #1044" by Quanyu Tang.

  This file states and proves the main theorems.
-/

open Polynomial MeasureTheory Topology Set Metric

noncomputable section

namespace Erdos1044

/-! ## Proposition 2.1: Lemniscate length of z^n - 1 -/

/-- **Proposition 2.1** (Classical). The model polynomial f_n(z) = z^n - 1 has Ω(f_n) with
    exactly n congruent connected components, each with boundary length L_n. -/
theorem modelPoly_boundary_length (n : ℕ) (hn : n ≥ 1) :
    LambdaFn (modelPoly n) = ENNReal.ofReal (lemniscateLength n) := by
  rw [lambdaFn_modelPoly_eq_single_component n hn]
  exact component_boundary_length_eq_lemniscateLength n hn

/-! ## Theorem 2.2: Upper bound -/

/-
**Theorem 2.2**. inf_f Λ(f) ≤ 2.
    Proof: Use the model polynomials f_n(z) = z^n - 1.
    By Proposition 2.1, Λ(f_n) = L_n → 2 as n → ∞.
-/
theorem lambdaInf_le_two : lambdaInf ≤ 2 := by
  unfold lambdaInf;
  refine le_trans ?_ ( show 2 ≥ ENNReal.ofReal 2 by norm_num );
  have h_lim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (lemniscateLength n)) Filter.atTop (nhds (ENNReal.ofReal 2)) := by
    refine ENNReal.tendsto_ofReal ?_;
    unfold lemniscateLength;
    -- We'll use the fact that $\Gamma(x) \approx \frac{1}{x}$ for $x$ close to $0$.
    have h_gamma_approx : Filter.Tendsto (fun n : ℕ => Real.Gamma (1 / (2 * (n : ℝ))) * (1 / (2 * (n : ℝ)))) Filter.atTop (nhds 1) := by
      have h_gamma_approx : Filter.Tendsto (fun x : ℝ => Real.Gamma x * x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have h_gamma_approx : Filter.Tendsto (fun x : ℝ => Real.Gamma (x + 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
          convert Filter.Tendsto.comp ( Real.differentiableAt_Gamma ?_ |> DifferentiableAt.continuousAt ) ( Filter.tendsto_id.add_const 1 |> Filter.Tendsto.mono_left <| nhdsWithin_le_nhds ) using 2 <;> norm_num;
          exact fun m => by linarith;
        refine h_gamma_approx.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ Real.Gamma_add_one hx.out.ne', mul_comm ] );
      refine h_gamma_approx.comp <| Filter.tendsto_inf.mpr ⟨ tendsto_const_nhds.div_atTop <| tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two, Filter.tendsto_principal.mpr <| Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by norm_num; linarith ⟩ ⟩;
    have h_gamma_approx : Filter.Tendsto (fun n : ℕ => Real.Gamma (1 / 2) * Real.Gamma (1 / (2 * (n : ℝ))) / Real.Gamma (1 / 2 + 1 / (2 * (n : ℝ))) * (1 / (2 * (n : ℝ)))) Filter.atTop (nhds (Real.Gamma (1 / 2) * 1 / Real.Gamma (1 / 2))) := by
      convert Filter.Tendsto.div ( h_gamma_approx.const_mul ( Real.Gamma ( 1 / 2 ) ) ) ( Filter.Tendsto.comp ( Real.differentiableAt_Gamma ?_ |> DifferentiableAt.continuousAt ) ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat.mul_const _ ) ) ) _ using 2 <;> norm_num;
      exacts [ by rw [ div_mul_eq_mul_div, mul_assoc ], rfl, fun m => by linarith, by positivity ];
    convert h_gamma_approx.mul ( show Filter.Tendsto ( fun n : ℕ => ( 2 : ℝ ) ^ ( 1 / ( n : ℝ ) ) * 2 ) Filter.atTop ( nhds 2 ) from ?_ ) using 2 <;> norm_num [ betaFn ] ; ring;
    · positivity;
    · simpa using Filter.Tendsto.mul ( tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat ( by norm_num ) ) tendsto_const_nhds;
  refine le_of_tendsto_of_tendsto tendsto_const_nhds h_lim ?_;
  filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn
  have h_admissible : IsAdmissible (modelPoly n) ∧ (modelPoly n).natDegree ≥ 1 := by
    refine ⟨ ⟨ ?_, ?_ ⟩, ?_ ⟩;
    · exact Polynomial.monic_X_pow_sub_C _ hn.ne';
    · unfold modelPoly;
      intro z hz; have := congr_arg Norm.norm ( show z ^ n = 1 by simpa [ sub_eq_iff_eq_add ] using hz ) ; norm_num at this ; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop;
    · erw [ Polynomial.natDegree_X_pow_sub_C ] ; linarith
  exact le_trans (ciInf_le ⟨0, Set.forall_mem_range.mpr fun f => by positivity⟩ (modelPoly n)) (by
  rw [ modelPoly_boundary_length n hn ] ; aesop)

/-! ## Section 3: Special case (roots on unit circle) -/

/-
If f is monic with all roots on the unit circle, then ‖f.eval 0‖ = 1.
-/
lemma norm_eval_zero_of_roots_on_circle (f : Polynomial ℂ) (hf : f.Monic)
    (hroots : ∀ z : ℂ, f.IsRoot z → ‖z‖ = 1) :
    ‖f.eval 0‖ = 1 := by
      nontriviality;
      have := @Polynomial.Splits.natDegree_eq_card_roots;
      specialize @this ℂ _ f _;
      rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hf ];
      · simp +decide [ Polynomial.eval_multiset_prod ];
        have h_prod_norm : ∀ {s : Multiset ℂ}, (∀ z ∈ s, ‖z‖ = 1) → ‖s.prod‖ = 1 := by
          intros s hs; induction s using Multiset.induction <;> aesop;
        exact h_prod_norm fun z hz => hroots z <| Polynomial.isRoot_of_mem_roots hz;
      · exact IsAlgClosed.card_roots_eq_natDegree

/-
For a non-constant polynomial f with ‖f.eval 0‖ = 1, there exist points
    arbitrarily close to 0 in OmegaSet f (minimum modulus principle).
-/
lemma zero_mem_closure_omegaSet (f : Polynomial ℂ)
    (hdeg : f.natDegree ≥ 1) (h_norm : ‖f.eval 0‖ = 1) :
    (0 : ℂ) ∈ closure (OmegaSet f) := by
      rw [ mem_closure_iff_nhds ];
      -- By contradiction, assume there exists an open set around 0 that does not intersect OmegaSet f.
      by_contra h_contra;
      -- Assume for contradiction that 0 is not in the closure of OmegaSet f.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ z, dist z 0 < δ → ‖f.eval z‖ ≥ 1 := by
        contrapose! h_contra;
        intro t ht; rcases Metric.mem_nhds_iff.mp ht with ⟨ δ, δ_pos, hδ ⟩ ; rcases h_contra δ δ_pos with ⟨ z, hz₁, hz₂ ⟩ ; exact ⟨ z, hδ hz₁, hz₂ ⟩ ;
      -- Since ‖f.eval z‖ ≥ 1 near 0, f.eval is locally constant near 0.
      have h_loc_const : ∀ᶠ z in nhds 0, f.eval z = f.eval 0 := by
        exact Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm ( by filter_upwards [ Metric.ball_mem_nhds _ hδ_pos ] with z hz using by exact f.differentiableAt ) ( Filter.eventually_of_mem ( Metric.ball_mem_nhds _ hδ_pos ) fun z hz => by aesop ) |> Or.resolve_right <| by aesop;
      -- Since f is a polynomial and is constant on a neighborhood of 0, it must be constant.
      have h_const : f = Polynomial.C (f.eval 0) := by
        have h_const : Set.Infinite {z : ℂ | f.eval z = f.eval 0} := by
          rw [ Metric.eventually_nhds_iff ] at h_loc_const;
          obtain ⟨ ε, ε_pos, hε ⟩ := h_loc_const;
          have h_const : Set.Infinite (Set.image (fun x : ℝ => x : ℝ → ℂ) (Set.Ioo 0 ε)) := by
            exact Set.Infinite.image ( fun x => by aesop ) ( Set.Ioo_infinite ε_pos );
          exact h_const.mono fun x hx => by obtain ⟨ y, hy, rfl ⟩ := hx; exact hε <| by simpa [ abs_of_pos hy.1 ] using hy.2;
        exact Classical.not_not.1 fun h => h_const <| Set.Finite.subset ( f - Polynomial.C ( f.eval 0 ) |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet ) fun x hx => by simp_all +decide [ sub_eq_iff_eq_add ] ;
      rw [ h_const ] at hdeg ; norm_num at hdeg

/-
**Theorem 3.2**. If f is monic of degree ≥ 1 with all roots on the unit circle, then Λ(f) ≥ 2.
    Note: the degree hypothesis is necessary since the constant polynomial 1 is monic
    with vacuously all roots on the unit circle, but LambdaFn(1) = 0.
-/
theorem lambda_ge_two_of_roots_on_circle (f : Polynomial ℂ) (hf : f.Monic)
    (hdeg : f.natDegree ≥ 1)
    (hroots : ∀ z : ℂ, f.IsRoot z → ‖z‖ = 1) :
    (2 : ENNReal) ≤ LambdaFn f := by
      -- By the pigeonhole argument, there exists a connected component $C$ of $\Omega(f)$ such that $0 \in \overline{C}$.
      obtain ⟨C, hC⟩ : ∃ C : Set ℂ, ∃ z : ℂ, z ∈ OmegaSet f ∧ C = connectedComponentIn (OmegaSet f) z ∧ (0 : ℂ) ∈ closure C := by
        obtain ⟨z, hz⟩ : ∃ z : ℂ, z ∈ OmegaSet f ∧ (0 : ℂ) ∈ closure (connectedComponentIn (OmegaSet f) z) := by
          obtain ⟨w, hw⟩ : ∃ w : ℕ → ℂ, (∀ n, w n ∈ OmegaSet f) ∧ Filter.Tendsto w Filter.atTop (nhds 0) := by
            have h_zero_mem_closure : (0 : ℂ) ∈ closure (OmegaSet f) := by
              exact zero_mem_closure_omegaSet f hdeg ( norm_eval_zero_of_roots_on_circle f hf hroots );
            rwa [ mem_closure_iff_seq_limit ] at h_zero_mem_closure;
          -- By the pigeonhole principle, there exists a root $r$ of $f$ such that infinitely many $w_n$ are in the connected component of $r$.
          obtain ⟨r, hr⟩ : ∃ r ∈ f.roots.toFinset, Set.Infinite {n | w n ∈ connectedComponentIn (OmegaSet f) r} := by
            have h_pigeonhole : Set.Infinite (⋃ r ∈ f.roots.toFinset, {n | w n ∈ connectedComponentIn (OmegaSet f) r}) := by
              refine Set.infinite_univ.mono fun n _ => ?_;
              obtain ⟨z, hz⟩ : ∃ z ∈ OmegaSet f, w n ∈ connectedComponentIn (OmegaSet f) z := by
                exact ⟨ w n, hw.1 n, mem_connectedComponentIn ( hw.1 n ) ⟩;
              have := component_contains_root f hf hdeg ( connectedComponentIn ( OmegaSet f ) z ) ?_ ?_ ?_ ?_ ?_ <;> simp_all +decide [ connectedComponentIn_subset ];
              · obtain ⟨ x, hx₁, hx₂ ⟩ := this; use x; simp_all +decide ;
                exact ⟨ hf.ne_zero, by rw [ connectedComponentIn_eq hx₁ ] at hz; exact hz.2 ⟩;
              · exact isPreconnected_connectedComponentIn;
              · exact IsOpen.connectedComponentIn ( omegaSet_isOpen f );
              · exact ⟨ _, hz.2 ⟩;
              · intro V hV₁ hV₂ hV₃ hV₄; exact (by
                apply le_antisymm;
                · apply_rules [ IsPreconnected.subset_connectedComponentIn ];
                  any_goals tauto;
                  all_goals exact hV₃ <| mem_connectedComponentIn <| by tauto;
                · exact hV₃);
            contrapose! h_pigeonhole;
            exact Set.Finite.biUnion ( Finset.finite_toSet _ ) h_pigeonhole;
          refine ⟨ r, ?_, ?_ ⟩;
          · unfold OmegaSet; aesop;
          · rw [ mem_closure_iff_seq_limit ];
            have := hr.2.exists_gt;
            choose g hg₁ hg₂ using this;
            exact ⟨ fun n => w ( g n ), fun n => hg₁ n, hw.2.comp ( Filter.tendsto_atTop_mono ( fun n => by linarith [ hg₂ n ] ) tendsto_natCast_atTop_atTop ) ⟩;
        exact ⟨ _, _, hz.1, rfl, hz.2 ⟩;
      -- By the pigeonhole argument, there exists a root $z_j$ of $f$ such that $z_j \in C$.
      obtain ⟨z_j, hz_j⟩ : ∃ z_j : ℂ, z_j ∈ C ∧ f.IsRoot z_j := by
        apply component_contains_root;
        any_goals tauto;
        · obtain ⟨ z, hz₁, rfl, hz₂ ⟩ := hC; exact isPreconnected_connectedComponentIn;
        · exact hC.choose_spec.2.1 ▸ IsOpen.connectedComponentIn ( omegaSet_isOpen f );
        · exact hC.choose_spec.2.1 ▸ connectedComponentIn_subset _ _;
        · exact hC.choose_spec.2.1.symm ▸ ⟨ _, mem_connectedComponentIn ( hC.choose_spec.1 ) ⟩;
        · intro V hV hV_open hV_sub hV_sub_Omega
          obtain ⟨z, hz⟩ := hC
          have hz_in_C : z ∈ C := by
            exact hz.2.1.symm ▸ mem_connectedComponentIn ( by aesop )
          have hz_in_V : z ∈ V := by
            exact hV_sub hz_in_C
          have hC_subset_V : C ⊆ V := by
            exact hV_sub
          have hV_subset_C : V ⊆ C := by
            rw [ hz.2.1 ];
            apply_rules [ IsPreconnected.subset_connectedComponentIn ]
          exact Set.Subset.antisymm hV_subset_C hC_subset_V;
      -- Since $C$ is a connected component of $\Omega(f)$, we have $\muH[1](\partial C) \geq 2 \cdot \text{diam}(C)$.
      have h_muH_ge_two_diam : μH[1] (frontier C) ≥ 2 * Metric.ediam C := by
        apply frontier_hausdorff_ge_two_ediam;
        · obtain ⟨ z, hz₁, rfl, hz₂ ⟩ := hC; exact IsOpen.connectedComponentIn ( omegaSet_isOpen f ) ;
        · obtain ⟨ z, hz₁, rfl, hz₂ ⟩ := hC;
          exact omegaSet_isBounded f hf hdeg |> fun h => h.subset <| connectedComponentIn_subset _ _;
        · exact ⟨ _, hz_j.1 ⟩;
        · rcases hC with ⟨ z, hz, rfl, hz' ⟩ ; exact ⟨ ⟨ z, mem_connectedComponentIn ( by aesop ) ⟩, isPreconnected_connectedComponentIn ⟩ ;
      -- Since $C$ is a connected component of $\Omega(f)$, we have $\text{diam}(C) \geq 1$.
      have h_diam_ge_one : Metric.ediam C ≥ 1 := by
        have h_diam_ge_one : edist 0 z_j ≤ Metric.ediam C := by
          have h_ediam_ge_one : edist 0 z_j ≤ Metric.ediam (closure C) := by
            apply Metric.edist_le_ediam_of_mem;
            · aesop;
            · exact subset_closure hz_j.1;
          rwa [ Metric.ediam_closure ] at h_ediam_ge_one;
        simp_all +decide [ edist_dist ];
      -- Since $C$ is a connected component of $\Omega(f)$, we have $\Lambda(f) \geq \muH[1](\partial C)$.
      have h_lambda_ge_muH : LambdaFn f ≥ μH[1] (frontier C) := by
        obtain ⟨ z, hz₁, rfl, hz₂ ⟩ := hC;
        exact le_iSup₂_of_le z hz₁ le_rfl;
      exact le_trans ( by exact le_trans ( by norm_num ) ( mul_le_mul_right h_diam_ge_one _ ) ) ( h_muH_ge_two_diam.trans h_lambda_ge_muH )

/-! ## Section 4: Main lower bound -/

/-
**Lemma 4.1**. Every connected component of Ω(f) contains at least one zero of f.
    In particular, Ω(f) has at most n connected components.
-/
-- Lemma 4.1 is now proved in ComponentRoot.lean.
-- Re-exported here for use in this file:
example := @Erdos1044.component_contains_root

/-
Special case of Pólya's theorem for degree 1: For f = X - C a (monic, degree 1),
    OmegaSet is ball(a,1), one connected component, diam = 2 ≥ 2.
-/
lemma polya_lemniscate_diam_deg_one (f : Polynomial ℂ) (hf : f.Monic)
    (hdeg : f.natDegree = 1) (z : ℂ) (hz : z ∈ OmegaSet f) :
    2 ≤ Metric.diam (connectedComponentIn (OmegaSet f) z) := by
      obtain ⟨c, hc⟩ : ∃ c : ℂ, f = Polynomial.X + Polynomial.C c := by
        rw [ Polynomial.eq_X_add_C_of_natDegree_le_one ( le_of_eq hdeg ) ];
        have := hf.coeff_natDegree; aesop;
      -- Since the set {z : ℂ | ‖z + c‖ < 1} is convex, it is connected.
      have h_connected : IsConnected {z : ℂ | ‖z + c‖ < 1} := by
        convert ( convex_ball ( -c : ℂ ) 1 ).isConnected ?_ using 1;
        · norm_num [ Set.ext_iff, dist_eq_norm ];
        · exact ⟨ -c, by norm_num ⟩;
      have h_connected_component : connectedComponentIn {z : ℂ | ‖z + c‖ < 1} z = {z : ℂ | ‖z + c‖ < 1} := by
        apply_rules [ IsPreconnected.connectedComponentIn ];
        · exact h_connected.isPreconnected;
        · unfold OmegaSet at hz; aesop;
      have h_diam : Metric.diam {z : ℂ | ‖z + c‖ < 1} = 2 := by
        have h_diam : Metric.diam (Metric.ball (-c) 1) = 2 := by
          have h_diam : Metric.diam (Metric.closedBall (-c) 1) = 2 := by
            convert diam_closedBall_eq _ _ using 1 <;> norm_num [ two_mul ];
            · infer_instance;
            · infer_instance;
          rw [ ← h_diam, ← closure_ball ];
          · exact Eq.symm (diam_closure (ball (-c) 1));
          · norm_num;
        convert h_diam using 2 ; ext ; simp +decide [ dist_eq_norm, add_comm ];
      unfold OmegaSet; aesop;

/-- **Pommerenke's component diameter bound**. For an admissible polynomial f
    (monic, all roots in the closed unit disk) of degree ≥ 1 with |f(0)| < 1,
    the connected component of Ω(f) containing 0 has diameter > 1.

    Note: the stronger claim that diam > 1 for *every* component (not just the one
    containing 0) is false in general. The hypothesis |f(0)| < 1 is essential. -/
theorem pommerenke_component_diam (f : Polynomial ℂ) (hf : IsAdmissible f)
    (hdeg : f.natDegree ≥ 1)
    (hf0 : ‖f.eval 0‖ < 1) :
    1 < Metric.diam (connectedComponentIn (OmegaSet f) 0) :=
  pommerenke_component_diam' f hf hdeg hf0

/-- **Pommerenke's Theorem** (cited from [5, Theorem 3], corrected statement).
    For an admissible polynomial f (monic, all roots in the closed unit disk)
    with |f(0)| < 1, the connected component of Ω(f) containing 0 has diameter > 1.

    Classical proof: Pommerenke (Math. Ann. 145, 1961) showed diam > 2 − r² where
    r = max|root| ≤ 1, giving diam > 1. The argument uses potential theory
    (logarithmic capacity, Green's functions) not yet available in Mathlib. -/
theorem pommerenke_diameter (f : Polynomial ℂ) (hf : IsAdmissible f)
    (hdeg : f.natDegree ≥ 1)
    (hf0 : ‖f.eval 0‖ < 1) :
    ∃ U : Set ℂ, (0 : ℂ) ∈ U ∧ U ⊆ OmegaSet f ∧ IsPreconnected U ∧
      1 < Metric.diam U := by
  have h0 : (0 : ℂ) ∈ OmegaSet f := by simpa [OmegaSet] using hf0
  exact ⟨connectedComponentIn (OmegaSet f) 0,
    mem_connectedComponentIn h0,
    connectedComponentIn_subset _ _,
    isPreconnected_connectedComponentIn,
    pommerenke_component_diam f hf hdeg hf0⟩

/-
Key algebraic lemma: if f is admissible and |f(0)| ≥ 1, then all roots are on the unit circle.
    Since f is monic over ℂ, f = ∏(X - C z_k) and |f(0)| = ∏|z_k|.
    With all |z_k| ≤ 1 and ∏|z_k| ≥ 1, each |z_k| must equal 1.
-/
lemma roots_on_circle_of_eval_zero_ge_one (f : Polynomial ℂ) (hf : IsAdmissible f)
    (_hf_deg : f.natDegree ≥ 1) (hf0 : 1 ≤ ‖f.eval 0‖) :
    ∀ z : ℂ, f.IsRoot z → ‖z‖ = 1 := by
      -- Since $f$ is monic and $|f(0)| \geq 1$, we have $f = \prod (X - C z_k)$ for some $z_k \in \mathbb{C}$ with $|z_k| \leq 1$.
      obtain ⟨z_k, hz_k⟩ : ∃ z_k : Multiset ℂ, f = Multiset.prod (Multiset.map (fun z => Polynomial.X - Polynomial.C z) z_k) ∧ ∀ z ∈ z_k, ‖z‖ ≤ 1 := by
        obtain ⟨z_k, hz_k⟩ : ∃ z_k : Multiset ℂ, f = Multiset.prod (Multiset.map (fun z => Polynomial.X - Polynomial.C z) z_k) := by
          have := IsAlgClosed.splits f;
          rw [ Polynomial.splits_iff_exists_multiset ] at this;
          exact ⟨ this.choose, by simpa [ hf.1.leadingCoeff ] using this.choose_spec ⟩;
        refine ⟨ z_k, hz_k, ?_ ⟩;
        intro z hz;
        exact hf.2 z ( by rw [ hz_k ] ; exact Multiset.exists_cons_of_mem hz |> fun ⟨ w, hw ⟩ => by simp +decide [ hw, Polynomial.eval_multiset_prod ] );
      -- Since $|f(0)| = \prod |z_k|$, and $|f(0)| \geq 1$, we have $\prod |z_k| \geq 1$.
      have h_prod : Multiset.prod (Multiset.map (fun z => ‖z‖) z_k) ≥ 1 := by
        simp_all +decide [ Polynomial.eval_multiset_prod ];
        -- By definition of product of norms, we have ‖z_k.prod‖ = Multiset.prod (Multiset.map (fun z => ‖z‖) z_k).
        have h_norm_prod : ∀ (ms : Multiset ℂ), ‖ms.prod‖ = Multiset.prod (Multiset.map (fun z => ‖z‖) ms) := by
          intro ms; induction ms using Multiset.induction <;> aesop;
        aesop;
      -- Since each factor ‖z_k‖ ∈ [0,1] and their product = 1, each ‖z_k‖ = 1.
      have h_each_one : ∀ z ∈ z_k, ‖z‖ = 1 := by
        intro z hz
        by_contra hz_ne_one;
        have h_prod_lt_one : Multiset.prod (Multiset.map (fun z => ‖z‖) z_k) < 1 := by
          have h_prod_lt_one : Multiset.prod (Multiset.map (fun z => ‖z‖) (z_k.erase z)) ≤ 1 := by
            have h_prod_lt_one : ∀ {m : Multiset ℂ}, (∀ z ∈ m, ‖z‖ ≤ 1) → Multiset.prod (Multiset.map (fun z => ‖z‖) m) ≤ 1 := by
              intros m hm; induction m using Multiset.induction <;> norm_num at *;
              exact mul_le_one₀ hm.1 ( Multiset.prod_nonneg ( by norm_num ) ) ( by apply_assumption; tauto );
            exact h_prod_lt_one fun x hx => hz_k.2 x <| Multiset.mem_of_mem_erase hx;
          rw [ ← Multiset.cons_erase hz, Multiset.map_cons, Multiset.prod_cons ];
          exact lt_of_le_of_lt ( mul_le_of_le_one_right ( norm_nonneg _ ) h_prod_lt_one ) ( lt_of_le_of_ne ( hz_k.2 z hz ) hz_ne_one );
        linarith;
      intro z hz; rw [ hz_k.1 ] at hz; simp_all +decide [ Polynomial.eval_multiset_prod ] ;
      obtain ⟨ a, ha, h ⟩ := hz; simpa [ sub_eq_zero.mp h ] using h_each_one a ha;

/-
**Theorem 4.3**. inf_f Λ(f) ≥ 2.

    Proof: Split into two cases.
    Case 1: |f(0)| < 1. Then 0 ∈ Ω(f). By Pommerenke's theorem, the component containing 0
    has diameter > 1. By Lemma 4.2 and Lemma 3.1, its boundary length > 2.
    Case 2: |f(0)| = 1. Then all |z_k| = 1, and Theorem 3.2 applies.
-/
theorem lambdaInf_ge_two : (2 : ENNReal) ≤ lambdaInf := by
  refine le_ciInf ?_;
  intro f
  by_cases h_deg : f.natDegree ≥ 1;
  · by_cases hf : IsAdmissible f <;> simp_all +decide;
    by_cases h_eval_zero : ‖f.eval 0‖ ≥ 1;
    · exact lambda_ge_two_of_roots_on_circle f hf.1 h_deg ( roots_on_circle_of_eval_zero_ge_one f hf h_deg h_eval_zero );
    · -- By pommerenke_diameter, there exists a connected component $U$ of $\Omega(f)$ containing $0$ with diameter $> 1$.
      obtain ⟨U, hU₀, hU₁, hU₂, hU₃⟩ : ∃ U : Set ℂ, (0 : ℂ) ∈ U ∧ U ⊆ OmegaSet f ∧ IsPreconnected U ∧ 1 < Metric.diam U := by
        apply pommerenke_diameter f hf h_deg (by
        exact lt_of_not_ge h_eval_zero);
      -- Let $C$ be the connected component of $\Omega(f)$ containing $0$.
      set C := connectedComponentIn (OmegaSet f) 0;
      -- Since $U$ is preconnected and contains $0$, we have $U \subseteq C$.
      have hU_subset_C : U ⊆ C := by
        apply_rules [ IsPreconnected.subset_connectedComponentIn ];
      -- Since $C$ is open, bounded, connected, and nonempty, we can apply Lemma 4.2 and Lemma 3.1 to get that the boundary length of $C$ is at least $2$.
      have hC_boundary_length : 2 ≤ μH[1] (frontier C) := by
        have hC_boundary_length : 2 * Metric.ediam C ≤ μH[1] (frontier C) := by
          apply frontier_hausdorff_ge_two_ediam;
          · apply_rules [ IsOpen.connectedComponentIn, omegaSet_isOpen ];
          · have hC_bounded : Bornology.IsBounded (OmegaSet f) := by
              apply Erdos1044.omegaSet_isBounded f hf.1 h_deg;
            exact hC_bounded.subset ( connectedComponentIn_subset _ _ );
          · exact ⟨ 0, mem_connectedComponentIn ( by aesop ) ⟩;
          · exact ⟨ ⟨ 0, mem_connectedComponentIn ( by aesop ) ⟩, isPreconnected_connectedComponentIn ⟩;
        refine le_trans ?_ hC_boundary_length;
        refine le_mul_of_one_le_right ( by norm_num ) ?_;
        refine le_trans ?_ ( Metric.ediam_mono hU_subset_C );
        contrapose! hU₃;
        convert ENNReal.toReal_mono _ hU₃.le using 1 ; norm_num [ ediam ];
      refine le_trans ?_ ( le_iSup₂_of_le 0 ?_ le_rfl );
      · exact hC_boundary_length;
      · exact hU₁ hU₀;
  · aesop

/-! ## Main Theorem: Solution to Problem 1.2 -/

/-- **Main Theorem** (Solution to Problem 1.2).
    inf_f Λ(f) = 2, where the infimum is over all monic polynomials with roots in
    the closed unit disk. -/
theorem erdos_problem_1044 : lambdaInf = 2 := by
  apply le_antisymm
  · exact lambdaInf_le_two
  · exact lambdaInf_ge_two

#print axioms erdos_problem_1044
-- 'Erdos1044.erdos_problem_1044' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1044
