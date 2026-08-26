/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 353.
Informal authors: Vjekoslav Kovač, Bruno Predojević.
Formal authors: Aristotle, JoshuaB.
Original Lean/Mathlib version: 4.28.0.
Source: https://www.erdosproblems.com/forum/thread/353#post-7098
Exact editor URL: data/urls.yaml, JoshuaB_353_polygon.
-/
import Mathlib

open MeasureTheory
open scoped BigOperators Real Nat Pointwise

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
/-!
# Polygons of unit area with vertices in sets of infinite planar measure
Formalization of Theorem `thm:congruent` from Kovač–Predojević,
"Polygons of unit area with vertices in sets of infinite planar measure".
There exists a planar set `S` of infinite Lebesgue measure such that every convex
polygon with congruent sides and all vertices in `S` has area strictly less than `1`.
The plane is `EuclideanSpace ℝ (Fin 2)`, so `dist` is the Euclidean distance and
`volume` is the planar Lebesgue (area) measure.  A convex polygon is given by its
cyclic sequence of vertices `C : ZMod n → EuclideanSpace ℝ (Fin 2)` (`n ≥ 3`); the
counter-clockwise convexity is expressed by the cross-product positivity condition,
its sides are the segments `[C i, C (i+1)]`, and its *area* is the Lebesgue measure
of the convex hull of the vertices.
## Proof status
The top-level statement `thm_congruent` is assembled from the lemmas below.  The
following analytic/measure-theoretic ingredients are fully proved:
`volume_Sset_top` (the set has infinite area), `volume_tri_prod` / `volume_tri`
(the area of a triangle cut from the axes), `hyparea_identity` (Lemma `lm:hyparea`),
`tri_convex`, and `exists_support_triangle` (the convex hull lies in the support
triangle).  The reduction `area_lt_one` is proved from the two lemmas below, with
the small-side (`a < 2`) case fully discharged.
`exists_support_line` (existence of the tangent/secant support line of the hyperbola
lying above all vertices) is now proved, by splitting on whether a common tangent
exists: the tangent (Case A) case is elementary, and the secant (`support_line_caseB`)
case is assembled from `caseB_minimizer` (`= caseB_min_point` + `caseB_contacts`, the
analytic minimizer of the support function) and `caseB_adjacent` (contiguity of the
maximizing face), the latter resting on `turn_left` and `chord_side` (convex position:
three cyclically-ordered vertices form a counter-clockwise triangle).
`chord_side` is now fully proved.  Note that it requires *strict* convexity
(`hsconv : ∀ i j, j ≠ i → j ≠ i + 1 → 0 < cross (C (i+1) - C i) (C j - C i)`), i.e. the
hypothesis that the vertices are in genuinely convex position (every non-adjacent
vertex lies strictly to the left of each edge).  This is the faithful notion of a
"convex polygon": under merely *weak* convexity (`0 ≤ cross …`, the original `hconv`)
the statement is in fact **false**, since weak convexity also admits degenerate
multiply-traced configurations.  For instance the "triangle traced twice"
`C = !«(0,0),(-1,0),(0,-1),(0,0),(-1,0),(0,-1)»` (n = 6) satisfies `hconv`, yet for
`a = 0, s = 2, t = 2` one computes `cross (C (a+4) - C a) (C (a+2) - C a) = 1 > 0`,
violating the conclusion.  Strict convexity excludes exactly these degenerate cases:
the lone remaining branch of the angle-sorting induction (`cross (g 1) (g m) = 0`)
becomes vacuous because `hsconv` forces `cross (g m) (g (n-1)) > 0`.
The strict-convexity hypothesis `hsconv` is threaded through `caseB_adjacent`,
`support_line_caseB`, `exists_support_line`, `exists_support_triangle`, `area_lt_one`
and the top-level `thm_congruent` (whose statement now characterises convex polygons
by strict convexity; the weak `hconv` is recovered internally where needed).
`area_lt_one_of_large` (the large-side `a ≥ 2` case) is now also fully proved, via a
width/total-variation argument rather than the paper's leftmost/rightmost adjacency
argument.  Assuming `1 ≤ area`, the support triangle gives `(x₁+x₂)² ≤ 2a²` and
`xmax ≤ x₁+x₂`.  Each side has horizontal extent `≥ √(a²-1/16)` (`edge_dx_ge`, vertices
lie in the strip `0 < y < 1/4`), and the total `x`-variation of the convex polygon is
`≤ 2·(xmax - xmin)` (`two_width_ge_sum`, cyclic unimodality of `x`).  Hence
`n·√(a²-1/16) ≤ 2(x₁+x₂) ≤ 2√2·a`, forcing `n < 3`, a contradiction.  The unimodality
rests on `x_valley` (the `x`-coordinate is a single valley when read from the rightmost
vertex), whose convex-position core is `no_interior_peak_alg` (an interior `x`-peak
below the maximum would make the two diagonals of a convex quadrilateral cross at a
point with contradictory `x`-coordinate).
The file is now `sorry`-free: `thm_congruent` and all supporting lemmas are proved
using only the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
-/
namespace Erdos353

namespace Kovac
/-- The 2×2 determinant / signed cross product of two planar vectors. -/
noncomputable def cross (u v : EuclideanSpace ℝ (Fin 2)) : ℝ := u 0 * v 1 - u 1 * v 0
/-- Membership predicate for the set `S = { (x,y) : x > 1, y > 0, 4xy < 1 }`. -/
def inS (p : EuclideanSpace ℝ (Fin 2)) : Prop := 1 < p 0 ∧ 0 < p 1 ∧ 4 * p 0 * p 1 < 1
/-- The set `S = { (x,y) : x > 1, y > 0, 4xy < 1 }`. -/
def Sset : Set (EuclideanSpace ℝ (Fin 2)) := {p | inS p}
/-
The set `S` has infinite planar Lebesgue measure.
-/
lemma measurableSet_Sset : MeasurableSet Sset := by
  classical
  unfold Sset inS
  measurability

theorem volume_Sset_top : volume Sset = ⊤ := by
  classical
  refine' eq_top_iff.mpr _;
  -- For each natural number `k ≥ 1`, consider the box where the first coordinate lies in `Ioo (k:ℝ) (k+1)` and the second coordinate lies in `Ioo 0 (1/(4*(k+1)))`.
  have h_boxes : ∀ k : ℕ, k ≥ 1 → volume {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))} = ENNReal.ofReal (1 / (4 * (k + 1))) := by
    intro k hk
    set box_k : Set (Fin 2 → ℝ) := {p : Fin 2 → ℝ | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))}
    have h_box_k : volume {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))} = volume box_k := by
      convert ( MeasureTheory.MeasurePreserving.measure_preimage ( show MeasureTheory.MeasurePreserving ( fun p : EuclideanSpace ℝ ( Fin 2 ) => p.ofLp ) volume volume from ?_ ) ?_ ) using 1;
      · rfl;
      · exact PiLp.volume_preserving_ofLp _;
      · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_lt measurable_const ( measurable_pi_apply 0 ) ) ( MeasurableSet.inter ( measurableSet_lt ( measurable_pi_apply 0 ) measurable_const ) ( MeasurableSet.inter ( measurableSet_lt measurable_const ( measurable_pi_apply 1 ) ) ( measurableSet_lt ( measurable_pi_apply 1 ) measurable_const ) ) ) );
    -- The volume of the box is the product of the lengths of its sides.
    have h_box_volume : volume box_k = ENNReal.ofReal ((k + 1 - k) * (1 / (4 * (k + 1)))) := by
      have h_box_volume : volume box_k = volume (Set.pi Set.univ fun i : Fin 2 => if i = 0 then Set.Ioo (k : ℝ) (k + 1) else Set.Ioo 0 (1 / (4 * (k + 1) : ℝ))) := by
        congr with p ; simp +decide [ Fin.forall_fin_two ] ; aesop;
      erw [ h_box_volume, MeasureTheory.Measure.pi_pi ] ; norm_num;
    aesop;
  -- Since these boxes are pairwise disjoint and their union is contained in `Sset`, we can apply the countable additivity of the volume measure.
  have h_union : volume (⋃ k : ℕ, ⋃ hk : k ≥ 1, {p : EuclideanSpace ℝ (Fin 2) | k < p 0 ∧ p 0 < k + 1 ∧ 0 < p 1 ∧ p 1 < 1 / (4 * (k + 1))}) = ∑' k : ℕ, if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0 := by
    rw [ MeasureTheory.measure_iUnion ];
    · congr with k ; aesop;
    · intro k l hkl; simp_all +decide [ Set.disjoint_left ] ;
      intro p hk₁ hk₂ hk₃ hk₄ hk₅ hl₁ hl₂ hl₃; contrapose! hkl; exact Nat.le_antisymm ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith } ) ( Nat.le_of_lt_succ <| by { rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith } ) ;
    · intro k; by_cases hk : 1 ≤ k <;> simp +decide [ hk ];
      fun_prop;
  -- Since the series $\sum_{k=1}^{\infty} \frac{1}{4(k+1)}$ diverges, we have $\sum' k : ℕ, if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0 = \top$.
  have h_diverges : ∑' k : ℕ, (if k ≥ 1 then ENNReal.ofReal (1 / (4 * (k + 1))) else 0) = ⊤ := by
    have h_diverges : ¬ Summable (fun k : ℕ => if k ≥ 1 then (1 / (4 * (k + 1) : ℝ)) else 0) := by
      erw [ ← summable_nat_add_iff 1 ] ; norm_num;
      erw [ summable_mul_right_iff ] <;> norm_num ; exact_mod_cast mt ( summable_nat_add_iff 2 |>.1 ) Real.not_summable_natCast_inv;
    contrapose! h_diverges;
    convert ENNReal.summable_toReal _;
    rotate_left;
    use fun k => if k ≥ 1 then ENNReal.ofReal ( 1 / ( 4 * ( k + 1 ) ) ) else 0;
    · convert h_diverges using 1;
    · split_ifs <;> norm_num [ ENNReal.toReal_ofReal ( by positivity : 0 ≤ ( 4 * ( ↑‹ℕ› + 1 ) : ℝ ) ⁻¹ ) ];
      rw [ ENNReal.toReal_ofReal ( by positivity ) ];
  refine' h_diverges ▸ h_union ▸ MeasureTheory.measure_mono _;
  simp +decide [ Set.subset_def, Sset ];
  intro p k hk₁ hk₂ hk₃ hk₄ hk₅; exact ⟨ by linarith [ show ( k : ℝ ) ≥ 1 by norm_cast ], hk₃, by norm_num at *; nlinarith [ mul_inv_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ) ] ⟩ ;
/-- The closed triangle cut from the first quadrant by the line with positive
`x`-intercept `p` and `y`-intercept `q`. -/
def tri (p q : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {z | 0 ≤ z 0 ∧ 0 ≤ z 1 ∧ z 0 / p + z 1 / q ≤ 1}
/-
The triangle `tri p q` is convex.
-/
theorem tri_convex (p q : ℝ) : Convex ℝ (tri p q) := by
  classical
  intro x hx y hy a b ha hb hab;
  simp_all +decide [ tri ];
  exact ⟨ by nlinarith, by nlinarith, by rw [ ← eq_sub_iff_add_eq' ] at hab; subst hab; ring_nf at *; nlinarith ⟩
/-
The same triangle, but as a subset of `ℝ × ℝ`.
-/
theorem volume_tri_prod (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    volume {z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1}
      = ENNReal.ofReal (p * q / 2) := by
  classical
  erw [ MeasureTheory.Measure.prod_apply ];
  · rw [ MeasureTheory.lintegral_congr_ae, MeasureTheory.lintegral_indicator ];
    change ∫⁻ x in Set.Icc 0 p, ENNReal.ofReal ( q * ( 1 - x / p ) ) = ENNReal.ofReal ( p * q / 2 );
    · rw [ ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ];
      · congr 1
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hp.le]
        have hfun : (fun x : ℝ => q * (1 - x / p)) = (fun x => q - (q / p) * x) := by
          funext x; field_simp
        rw [hfun, intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 p)
            (Continuous.intervalIntegrable (by fun_prop) 0 p), intervalIntegral.integral_const,
            intervalIntegral.integral_const_mul, integral_id]
        simp only [smul_eq_mul]; field_simp; ring
      · exact Continuous.integrableOn_Icc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using mul_nonneg hq.le ( sub_nonneg.2 <| div_le_one_of_le₀ hx.2 hp.le );
    · norm_num;
    · filter_upwards [ ] with x ; by_cases hx : 0 ≤ x <;> by_cases hx' : x ≤ p <;> simp +decide [ *, Set.indicator ];
      · rw [ show { a : ℝ | 0 ≤ a ∧ x / p + a / q ≤ 1 } = Set.Icc 0 ( q * ( 1 - x / p ) ) from ?_ ];
        · simp +decide [ Real.volume_Icc ];
        · exact Set.ext fun y => ⟨ fun hy => ⟨ hy.1, by nlinarith [ hy.2, mul_div_cancel₀ x hp.ne', mul_div_cancel₀ y hq.ne' ] ⟩, fun hy => ⟨ hy.1, by nlinarith [ hy.2, mul_div_cancel₀ x hp.ne', mul_div_cancel₀ y hq.ne' ] ⟩ ⟩;
      · exact MeasureTheory.measure_mono_null ( fun y hy => by nlinarith [ hy.1, hy.2, div_mul_cancel₀ x hp.ne', div_mul_cancel₀ y hq.ne', mul_pos hp hq ] ) ( MeasureTheory.measure_empty );
  · exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) ( measurableSet_le ( measurable_fst.div_const p |> Measurable.add <| measurable_snd.div_const q ) measurable_const ) )
/-
The area of the triangle `tri p q` is `p*q/2`.
-/
theorem volume_tri (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    volume (tri p q) = ENNReal.ofReal (p * q / 2) := by
  classical
  -- The set `tri p q` is the preimage of the set `{z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1}` under the map `e := (volume_preserving_finTwoArrow ℝ).comp PiLp.volume_preserving_ofLp`.
  set e : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ := fun z => (z 0, z 1);
  rw [ show tri p q = e ⁻¹' { z : ℝ × ℝ | 0 ≤ z.1 ∧ 0 ≤ z.2 ∧ z.1 / p + z.2 / q ≤ 1 } from ?_ ];
  · convert volume_tri_prod p q hp hq using 1;
    convert ( MeasureTheory.MeasurePreserving.measure_preimage <| ?_ ) _;
    · exact (MeasureTheory.volume_preserving_finTwoArrow ℝ).comp
        (PiLp.volume_preserving_ofLp (Fin 2))
    · exact MeasurableSet.nullMeasurableSet ( by exact MeasurableSet.inter ( measurableSet_le measurable_const measurable_fst ) ( MeasurableSet.inter ( measurableSet_le measurable_const measurable_snd ) ( measurableSet_le ( measurable_fst.div_const p |> Measurable.add <| measurable_snd.div_const q ) measurable_const ) ) );
  · aesop
/-
Algebraic identity behind Lemma `lm:hyparea`: the triangle the secant of the
hyperbola `4xy=1` through `(x₁,1/(4x₁))` and `(x₂,1/(4x₂))` cuts from the axes has
area `(x₁+x₂)²/(8 x₁ x₂) = 1/2 + (x₁-x₂)²/(8 x₁ x₂)`.
-/
theorem hyparea_identity (x1 x2 : ℝ) (h1 : 0 < x1) (h2 : 0 < x2) :
    (x1 + x2) ^ 2 / (8 * x1 * x2) = 1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2) := by
  classical
  have h : (8 : ℝ) * x1 * x2 ≠ 0 := by positivity
  field_simp
  ring
/-
**Analytic core of Case B.**  When for every contact `t ≥ 1` some vertex lies
strictly above the tangent `x + 4t²y = 2t`, the support function
`h t = ⨆ᵢ (C i 0 + 4t² · C i 1 - 2t)` is positive and coercive on `[1,∞)`, hence
attains a positive minimum `m` at some `t > 1`.  At that minimizer two vertices attain
the maximum, one with `8 · C iR 1 · t ≤ 2` (`y ≤ 1/(4t)`) and one with
`2 ≤ 8 · C iL 1 · t` (`y ≥ 1/(4t)`): these are the two contacts of the narrowest
secant support line.
-/
theorem caseB_min_point
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ (t m : ℝ), 1 < t ∧ 0 < m ∧
      (∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m) ∧
      (∀ s : ℝ, 1 ≤ s → ∃ i : ZMod n, m ≤ C i 0 + 4 * s ^ 2 * C i 1 - 2 * s) := by
  classical
  revert hB;
  intro hB
  have : NeZero n := ⟨by linarith⟩
  set h : ℝ → ℝ := fun s => Finset.univ.sup' Finset.univ_nonempty (fun i => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) with hh_def
  have h_cont : Continuous h := by
    fun_prop
  have h_pos : ∀ s : ℝ, 1 ≤ s → 0 < h s := by
    intro s hs; obtain ⟨ i, hi ⟩ := hB s hs; exact lt_of_lt_of_le ( by linarith ) ( Finset.le_sup' ( fun i => ( C i |> fun x => x.ofLp 0 + 4 * s ^ 2 * x.ofLp 1 - 2 * s ) ) ( Finset.mem_univ i ) ) ;
  have h_coercive : Filter.Tendsto h Filter.atTop Filter.atTop := by
    -- Fix an arbitrary $i0$.
    obtain ⟨i0, hi0⟩ : ∃ i0 : ZMod n, 0 < (C i0) 1 := by
      exact ⟨ 0, hS 0 |>.2.1 ⟩;
    -- Since $4 * (C i0) 1 > 0$, we have $h(s) \geq (C i0) 0 + 4 * s^2 * (C i0) 1 - 2 * s$.
    have h_lower_bound : ∀ s : ℝ, 1 ≤ s → h s ≥ (C i0) 0 + 4 * s^2 * (C i0) 1 - 2 * s := by
      exact fun s hs => Finset.le_sup' ( fun i => ( C i |> fun x => x.ofLp 0 ) + 4 * s ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * s ) ( Finset.mem_univ i0 );
    refine' Filter.tendsto_atTop.mpr _;
    intro b; filter_upwards [ Filter.eventually_ge_atTop 1, Filter.eventually_gt_atTop ( ( |b - ( C i0 |> fun x => x.ofLp 0 )| + 2 ) / ( 4 * ( C i0 |> fun x => x.ofLp 1 ) ) + 1 ) ] with s hs₁ hs₂; cases abs_cases ( b - ( C i0 |> fun x => x.ofLp 0 ) ) <;> nlinarith [ h_lower_bound s hs₁, mul_div_cancel₀ ( |b - ( C i0 |> fun x => x.ofLp 0 )| + 2 ) ( by positivity : ( 4 * ( C i0 |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_le_mul_of_nonneg_left hs₂.le hi0.le ] ;
  obtain ⟨t, ht⟩ : ∃ t : ℝ, 1 < t ∧ ∀ s : ℝ, 1 ≤ s → h t ≤ h s := by
    -- Since $h$ is continuous and coercive, it must attain a global minimum on $[1, \infty)$.
    obtain ⟨t, ht⟩ : ∃ t : ℝ, 1 ≤ t ∧ ∀ s : ℝ, 1 ≤ s → h t ≤ h s := by
      -- By the properties of continuous functions on compact intervals, $h$ attains its minimum on $[1, M]$ for some $M > 1$.
      obtain ⟨M, hM⟩ : ∃ M : ℝ, 1 < M ∧ ∀ s : ℝ, M ≤ s → h s > h 1 := by
        exact Filter.eventually_atTop.mp ( h_coercive.eventually_gt_atTop ( h 1 ) ) |> fun ⟨ M, hM ⟩ ↦ ⟨ Max.max M 2, by norm_num, fun s hs ↦ hM s ( le_trans ( le_max_left _ _ ) hs ) ⟩;
      -- By the properties of continuous functions on compact intervals, $h$ attains its minimum on $[1, M]$.
      obtain ⟨t, ht⟩ : ∃ t ∈ Set.Icc 1 M, ∀ s ∈ Set.Icc 1 M, h t ≤ h s := by
        exact ( IsCompact.exists_isMinOn ( CompactIccSpace.isCompact_Icc ) ⟨ 1, Set.left_mem_Icc.mpr hM.1.le ⟩ h_cont.continuousOn );
      exact ⟨ t, ht.1.1, fun s hs => if hs' : s ≤ M then ht.2 s ⟨ hs, hs' ⟩ else by linarith [ hM.2 s ( le_of_not_ge hs' ), ht.2 1 ⟨ by norm_num, by linarith ⟩ ] ⟩;
    by_cases ht_eq_one : t = 1;
    · -- For each `i`, `φ i` is the parabola `4*C i 1*s^2 - 2*s + C i 0` whose derivative at `s = 1` is `8*C i 1 - 2 < 0` (as `C i 1 < 1/4`); so each `φ i` is strictly decreasing immediately to the right of `1`.
      have h_deriv_neg : ∀ i : ZMod n, deriv (fun s : ℝ => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) 1 < 0 := by
        intro i
        have hd : HasDerivAt (fun s : ℝ => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s)
            (8 * (C i) 1 - 2) 1 := by
          convert (((hasDerivAt_pow 2 (1 : ℝ)).const_mul 4).mul_const ((C i) 1)
            |>.const_add ((C i) 0)).sub ((hasDerivAt_id (1 : ℝ)).const_mul 2) using 1 <;> try rfl
          norm_num
        rw [hd.deriv]
        nlinarith [ hS i |>.1, hS i |>.2.1, hS i |>.2.2 ]
      -- Since each `φ i` is strictly decreasing immediately to the right of `1`, there exists a `δ > 0` such that for all `s ∈ (1, 1 + δ)`, `φ i s < φ i 1`.
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), ∀ i : ZMod n, (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
        have h_deriv_neg : ∀ i : ZMod n, ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
          intro i
          have h_deriv_neg_i : deriv (fun s : ℝ => (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s) 1 < 0 := h_deriv_neg i
          have h_deriv_neg_i_pos : ∃ δ > 0, ∀ s ∈ Set.Ioo 1 (1 + δ), (C i) 0 + 4 * s^2 * (C i) 1 - 2 * s < (C i) 0 + 4 * 1^2 * (C i) 1 - 2 * 1 := by
            have := Metric.tendsto_nhdsWithin_nhds.mp ( HasDerivAt.tendsto_slope_zero ( hasDerivAt_deriv_iff.mpr <| show DifferentiableAt ℝ ( fun s : ℝ => ( C i |> fun x => x.ofLp 0 ) + 4 * s ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * s ) 1 from by fun_prop ) );
            obtain ⟨ δ, hδ₁, H ⟩ := this _ ( neg_pos.mpr h_deriv_neg_i ) ; use δ, hδ₁; intro s hs; have := H ( show ( s - 1 ) ≠ 0 from sub_ne_zero.mpr hs.1.ne' ) ( abs_lt.mpr ⟨ by linarith [ hs.1, hs.2 ], by linarith [ hs.1, hs.2 ] ⟩ ) ; norm_num at *;
            nlinarith [ abs_lt.mp this, inv_mul_cancel₀ ( by linarith : ( s - 1 ) ≠ 0 ) ]
          exact h_deriv_neg_i_pos;
        choose δ hδ_pos hδ using h_deriv_neg;
        -- Since there are finitely many `i`, we can take the minimum of the `δ i`'s.
        obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ i : ZMod n, δ_min ≤ δ i := by
          have h_min : ∃ i : ZMod n, ∀ j : ZMod n, δ i ≤ δ j := by
            simpa using Finset.exists_min_image Finset.univ ( fun i => δ i ) ⟨ 0, Finset.mem_univ 0 ⟩;
          exact ⟨ δ h_min.choose, hδ_pos _, h_min.choose_spec ⟩;
        exact ⟨ δ_min, hδ_min_pos, fun s hs i => hδ i s ⟨ hs.1, by linarith [ hs.2, hδ_min i ] ⟩ ⟩;
      -- Since `h` is the supremum of the `φ i` functions, and each `φ i` is strictly decreasing immediately to the right of `1`, `h` must also be strictly decreasing immediately to the right of `1`.
      have h_h_decreasing : ∀ s ∈ Set.Ioo 1 (1 + δ), h s < h 1 := by
        intro s hs
        apply (Finset.sup'_lt_iff _).mpr
        intro i hi
        exact (hδ s hs i).trans_le (Finset.le_sup' (fun j => (C j) 0 + 4 * 1^2 * (C j) 1 - 2 * 1) (Finset.mem_univ i))
      exact absurd ( h_h_decreasing ( 1 + δ / 2 ) ⟨ by linarith, by linarith ⟩ ) ( by subst ht_eq_one; linarith [ ht.2 ( 1 + δ / 2 ) ( by linarith ) ] );
    · exact ⟨ t, lt_of_le_of_ne ht.1 ( Ne.symm ht_eq_one ), ht.2 ⟩
  use t, h t;
  simp +zetaDelta at *;
  exact ⟨ ht.1, h_pos t ht.1.le, fun i => ⟨ i, le_rfl ⟩, ht.2 ⟩
/-
**Contact extraction.**  At an interior global minimizer `t > 1` of the support
function (value `m`, with `hsup` the upper bound and `hglob` global minimality), two
active vertices straddle the tangency height `1/(4t)`: one with `8·C iR 1·t ≤ 2` and
one with `2 ≤ 8·C iL 1·t`.  This is the one-sided derivative test for the kinked
minimum.
-/
theorem caseB_contacts
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (t m : ℝ) (ht1 : 1 < t)
    (hsup : ∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m)
    (hglob : ∀ s : ℝ, 1 ≤ s → ∃ i : ZMod n, m ≤ C i 0 + 4 * s ^ 2 * C i 1 - 2 * s) :
    (∃ iR : ZMod n, C iR 0 + 4 * t ^ 2 * C iR 1 - 2 * t = m ∧ 8 * C iR 1 * t ≤ 2) ∧
    (∃ iL : ZMod n, C iL 0 + 4 * t ^ 2 * C iL 1 - 2 * t = m ∧ 2 ≤ 8 * C iL 1 * t) := by
  classical
  constructor;
  · by_contra! h_contra;
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, δ < t - 1 ∧ ∀ i, (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ) < m := by
      have hδ_exists : ∀ i, ∃ δ_i > 0, ∀ δ, 0 < δ ∧ δ < δ_i → (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ) < m := by
        intro i
        by_cases hi : (C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t = m;
        · use (8 * (C i).ofLp 1 * t - 2) / (8 * (C i).ofLp 1);
          exact ⟨ div_pos ( by linarith [ h_contra i hi ] ) ( by linarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ] ), fun δ hδ => by nlinarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1, mul_div_cancel₀ ( 8 * ( C i |> fun x => x.ofLp 1 ) * t - 2 ) ( by linarith [ h_contra i hi, show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ] : ( 8 * ( C i |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_pos hδ.1 ( show 0 < ( C i |> fun x => x.ofLp 1 ) from by have := hS i; exact this.2.1 ) ] ⟩;
        · have hδ_exists : Filter.Tendsto (fun δ => (C i).ofLp 0 + 4 * (t - δ) ^ 2 * (C i).ofLp 1 - 2 * (t - δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t)) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
          have := Metric.tendsto_nhdsWithin_nhds.mp hδ_exists ( m - ( ( C i |> fun x => x.ofLp 0 ) + 4 * t ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * t ) ) ( sub_pos.mpr <| lt_of_le_of_ne ( hsup i ) hi );
          exact ⟨ this.choose, this.choose_spec.1, fun δ hδ => by linarith [ abs_lt.mp ( this.choose_spec.2 hδ.1 ( by simpa [ abs_of_pos hδ.1 ] using hδ.2 ) ) ] ⟩;
      choose δ hδ_pos hδ using hδ_exists;
      obtain ⟨δ_min, hδ_min_pos, hδ_min⟩ : ∃ δ_min > 0, ∀ i, δ_min ≤ δ i := by
        cases n <;> [ tauto; exact ⟨ Finset.min' ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩, by have := Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ ; aesop, fun i => Finset.min'_le _ _ <| Finset.mem_image_of_mem δ <| Finset.mem_univ i ⟩ ];
      exact ⟨ Min.min δ_min ( t - 1 ) / 2, by linarith [ lt_min hδ_min_pos ( sub_pos.mpr ht1 ) ], by linarith [ min_le_left δ_min ( t - 1 ), min_le_right δ_min ( t - 1 ) ], fun i => hδ i _ ⟨ by linarith [ lt_min hδ_min_pos ( sub_pos.mpr ht1 ) ], by linarith [ min_le_left δ_min ( t - 1 ), min_le_right δ_min ( t - 1 ), hδ_min i ] ⟩ ⟩;
    exact absurd ( hglob ( t - δ ) ( by linarith ) ) ( by rintro ⟨ i, hi ⟩ ; linarith [ hδ.2 i ] );
  · contrapose! hglob;
    -- Choose $s = t + \delta$ for some small $\delta > 0$.
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ i : ZMod n, (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ) < m := by
      have h_cont : ∀ i : ZMod n, ∃ δ_i > 0, ∀ δ, 0 < δ ∧ δ < δ_i → (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ) < m := by
        intro i
        by_cases h_eq : (C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t = m;
        · exact ⟨ ( 2 - 8 * ( C i |> fun x => x.ofLp 1 ) * t ) / ( 8 * ( C i |> fun x => x.ofLp 1 ) ), div_pos ( by linarith [ hglob i h_eq ] ) ( mul_pos ( by norm_num ) ( by linarith [ hS i |>.2.1 ] ) ), fun δ hδ => by nlinarith [ hglob i h_eq, hδ.1, hδ.2, mul_div_cancel₀ ( 2 - 8 * ( C i |> fun x => x.ofLp 1 ) * t ) ( by linarith [ hS i |>.2.1 ] : ( 8 * ( C i |> fun x => x.ofLp 1 ) ) ≠ 0 ), mul_pos hδ.1 ( by linarith [ hS i |>.2.1 ] : 0 < ( C i |> fun x => x.ofLp 1 ) ) ] ⟩;
        · have h_cont : Filter.Tendsto (fun δ => (C i).ofLp 0 + 4 * (t + δ) ^ 2 * (C i).ofLp 1 - 2 * (t + δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((C i).ofLp 0 + 4 * t ^ 2 * (C i).ofLp 1 - 2 * t)) := by
            exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
          have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( m - ( ( C i |> fun x => x.ofLp 0 ) + 4 * t ^ 2 * ( C i |> fun x => x.ofLp 1 ) - 2 * t ) ) ( sub_pos.mpr <| lt_of_le_of_ne ( hsup i ) h_eq );
          exact ⟨ this.choose, this.choose_spec.1, fun δ hδ => by linarith [ abs_lt.mp ( this.choose_spec.2 hδ.1 ( by simpa [ abs_of_pos hδ.1 ] using hδ.2 ) ) ] ⟩;
      choose δ hδ_pos hδ using h_cont;
      cases n <;> norm_num at *;
      exact ⟨ Finset.min' ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ / 2, half_pos ( Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ |> fun x => by aesop ), fun i => hδ i _ ( half_pos ( Finset.min'_mem ( Finset.univ.image δ ) ⟨ _, Finset.mem_image_of_mem δ ( Finset.mem_univ 0 ) ⟩ |> fun x => by aesop ) ) ( by linarith [ Finset.min'_le _ _ ( Finset.mem_image_of_mem δ ( Finset.mem_univ i ) ), hδ_pos i ] ) ⟩;
    exact ⟨ t + δ, by linarith, hδ ⟩
/-- **Analytic core of Case B.**  Combines `caseB_min_point` and `caseB_contacts`:
the support function attains a positive minimum at some `t > 1`, where two vertices
attain the maximum straddling the tangency height `1/(4t)`. -/
theorem caseB_minimizer
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ (t m : ℝ), 1 < t ∧ 0 < m ∧
      (∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 - 2 * t ≤ m) ∧
      (∃ iR : ZMod n, C iR 0 + 4 * t ^ 2 * C iR 1 - 2 * t = m ∧ 8 * C iR 1 * t ≤ 2) ∧
      (∃ iL : ZMod n, C iL 0 + 4 * t ^ 2 * C iL 1 - 2 * t = m ∧ 2 ≤ 8 * C iL 1 * t) := by
  classical
  obtain ⟨t, m, ht1, hm, hsup, hglob⟩ := caseB_min_point n C hn hS hB
  obtain ⟨hR, hL⟩ := caseB_contacts n C hn hS t m ht1 hsup hglob
  exact ⟨t, m, ht1, hm, hsup, hR, hL⟩
/-
Consecutive edges of a counter-clockwise convex polygon turn left.
-/
theorem turn_left
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i)) :
    ∀ i : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C (i + 1 + 1) - C (i + 1)) := by
  classical
  intro i;
  -- Apply `hconv` with `j = i + 1 + 1`.
  specialize hconv i (i + 1 + 1);
  unfold cross at *; norm_num at *; linarith;
/-- **Chord-side / convex position.**  For a counter-clockwise convex polygon
(`hconv`), three vertices in cyclic order `a`, `a+s`, `a+s+t` (with `s, t ≥ 1` and
`s + t < n`) form a counter-clockwise triangle: the middle vertex `a+s` lies weakly to
the right of the directed chord `a → a+s+t`. -/
theorem chord_side
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (a : ZMod n) (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hst : s + t < n) :
    cross (C (a + ((s + t : ℕ) : ZMod n)) - C a) (C (a + (s : ZMod n)) - C a) ≤ 0 := by
  classical
  have : NeZero n := ⟨by omega⟩
  set g : ℕ → EuclideanSpace ℝ (Fin 2) := fun k => C (a + (k : ZMod n)) - C a with hg
  have hcastn : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h0 : ((n - 1 : ℕ) : ZMod n) + 1 = 0 := by
      rw [← Nat.cast_one (R := ZMod n), ← Nat.cast_add, Nat.sub_add_cancel (by omega)]
      exact ZMod.natCast_self n
    exact eq_neg_of_add_eq_zero_left h0
  -- All chords `g k = C (a+k) - C a` are weakly left of the first edge `g 1 = e_a` …
  have hA : ∀ k : ℕ, 0 ≤ cross (g 1) (g k) := by
    intro k; have := hconv a (a + (k : ZMod n)); simpa [hg, Nat.cast_one] using this
  -- … consecutive fan triangles at `a` are counter-clockwise …
  have hB : ∀ k : ℕ, 0 ≤ cross (g k) (g (k + 1)) := by
    intro k
    have h := hconv (a + (k : ZMod n)) a
    have hcast : ((k + 1 : ℕ) : ZMod n) = (k : ZMod n) + 1 := by push_cast; ring
    have he : cross (g k) (g (k + 1))
        = cross (C (a + (k : ZMod n) + 1) - C (a + (k : ZMod n))) (C a - C (a + (k : ZMod n))) := by
      simp only [hg, hcast]; unfold cross; simp [PiLp.sub_apply]; ring_nf
    rw [he]; have h2 : a + (k : ZMod n) + 1 = (a + (k : ZMod n)) + 1 := by ring
    rw [h2]; exact h
  -- … and all `g k` are weakly left of the last edge `g (n-1) = -e_{a-1}`.
  have hC : ∀ k : ℕ, 0 ≤ cross (g k) (g (n - 1)) := by
    intro k
    have h := hconv (a - 1) (a + (k : ZMod n))
    have heq : a - 1 + 1 = a := by ring
    rw [heq] at h
    have he : cross (g k) (g (n - 1))
        = cross (C a - C (a - 1)) (C (a + (k : ZMod n)) - C (a - 1)) := by
      simp only [hg, hcastn]
      have h3 : a + (-1 : ZMod n) = a - 1 := by ring
      rw [h3]; unfold cross; simp [PiLp.sub_apply]; ring
    rw [he]; exact h
  -- Angle sorting: `0 ≤ cross (g s) (g m)` for `s ≤ m ≤ s+t`, by induction on `m`.
  have key : ∀ m : ℕ, s ≤ m → m ≤ s + t → 0 ≤ cross (g s) (g m) := by
    intro m hsm hmst
    induction m, hsm using Nat.le_induction with
    | base => have h0 : cross (g s) (g s) = 0 := by unfold cross; ring
              rw [h0]
    | succ m hm ih =>
      have ihv := ih (by omega)
      -- two Grassmann–Plücker relations (references `g 1` and `g (n-1)`)
      have P1 : cross (g 1) (g m) * cross (g s) (g (m + 1))
          = cross (g 1) (g (m + 1)) * cross (g s) (g m)
            + cross (g 1) (g s) * cross (g m) (g (m + 1)) := by unfold cross; ring
      have P2 : cross (g m) (g (n - 1)) * cross (g s) (g (m + 1))
          = cross (g (m + 1)) (g (n - 1)) * cross (g s) (g m)
            + cross (g s) (g (n - 1)) * cross (g m) (g (m + 1)) := by unfold cross; ring
      have hsum : (cross (g 1) (g m) + cross (g m) (g (n - 1))) * cross (g s) (g (m + 1))
          = (cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1))) * cross (g s) (g m)
            + (cross (g 1) (g s) + cross (g s) (g (n - 1))) * cross (g m) (g (m + 1)) := by
        nlinarith [P1, P2]
      have hP : 0 ≤ cross (g 1) (g m) + cross (g m) (g (n - 1)) := by
        have := hA m; have := hC m; linarith
      have hRHS : 0 ≤ (cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1))) * cross (g s) (g m)
            + (cross (g 1) (g s) + cross (g s) (g (n - 1))) * cross (g m) (g (m + 1)) := by
        have h1 := hA (m + 1); have h2 := hC (m + 1); have h3 := hA s; have h4 := hC s
        have h5 := hB m
        have hc1 : 0 ≤ cross (g 1) (g (m + 1)) + cross (g (m + 1)) (g (n - 1)) := by linarith
        have hc2 : 0 ≤ cross (g 1) (g s) + cross (g s) (g (n - 1)) := by linarith
        have := mul_nonneg hc1 ihv; have := mul_nonneg hc2 h5; linarith
      rcases lt_or_eq_of_le hP with hPpos | hPzero
      · -- generic case: the combined coefficient is positive, so divide
        have hX : 0 ≤ (cross (g 1) (g m) + cross (g m) (g (n - 1))) * cross (g s) (g (m + 1)) := by
          rw [hsum]; exact hRHS
        by_contra hcon; push Not at hcon
        nlinarith [mul_pos hPpos (neg_pos.mpr hcon)]
      · -- degenerate case `cross (g 1) (g m) = cross (g m) (g (n-1)) = 0`
        -- (the chord `g m` would be parallel to both bounding edges).  Under strict
        -- convexity (`hsconv`) this is impossible: `cross (g m) (g (n-1)) > 0`,
        -- contradicting `hPzero`.
        exfalso
        have hm_lb : 1 ≤ m := le_trans hs hm
        have hm_ub : m ≤ n - 2 := by omega
        -- `(m : ZMod n) ≠ 0` and `≠ -1` since `1 ≤ m ≤ n-2`.
        have hne0 : (m : ZMod n) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd; have := Nat.le_of_dvd (by omega) hdvd; omega
        have hnen1 : (m : ZMod n) ≠ -1 := by
          rw [Ne, ← hcastn, ZMod.natCast_eq_natCast_iff]
          intro h
          have h' : m % n = (n - 1) % n := h
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
          omega
        have hne_a : a + (m : ZMod n) ≠ a - 1 := by
          intro hcon; apply hnen1
          have h2 : a + (m : ZMod n) = a + (-1) := by rw [hcon]; ring
          exact add_left_cancel h2
        have hne_a2 : a + (m : ZMod n) ≠ a := by
          intro hcon; apply hne0
          have h2 : a + (m : ZMod n) = a + 0 := by rw [hcon]; ring
          exact add_left_cancel h2
        have hpos : 0 < cross (g m) (g (n - 1)) := by
          have h := hsconv (a - 1) (a + (m : ZMod n)) hne_a
            (by rw [show a - 1 + 1 = a from by ring]; exact hne_a2)
          rw [show a - 1 + 1 = a from by ring] at h
          have he : cross (g m) (g (n - 1))
              = cross (C a - C (a - 1)) (C (a + (m : ZMod n)) - C (a - 1)) := by
            simp only [hg, hcastn]
            have h3 : a + (-1 : ZMod n) = a - 1 := by ring
            rw [h3]; unfold cross; simp [PiLp.sub_apply]; ring
          rw [he]; exact h
        have h1 : 0 ≤ cross (g 1) (g m) := hA m
        linarith [hPzero]
  -- transfer back to the stated goal
  have hfin := key (s + t) (by omega) (by omega)
  have hgoal : cross (C (a + ((s + t : ℕ) : ZMod n)) - C a) (C (a + (s : ZMod n)) - C a)
       = - cross (g s) (g (s + t)) := by
    simp only [hg]; unfold cross; simp [PiLp.sub_apply]; ring
  rw [hgoal]; linarith
/-
**Contiguity of the maximizing face.**  For a counter-clockwise convex polygon
(`hconv`) and the linear functional `ℓ z = z 0 + c · z 1`, the vertices attaining the
maximum value `d` form a single edge.  If the maximizers split (via `hstrip`) into a
`≤ lo` group (witnessed by `L`) and a `≥ hi` group (witnessed by `R`) with `lo < hi`,
then some side `(k, k+1)` joins the two groups.
-/
theorem caseB_adjacent
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (c d lo hi : ℝ)
    (hsupp : ∀ j : ZMod n, C j 0 + c * C j 1 ≤ d)
    (hstrip : ∀ j : ZMod n, C j 0 + c * C j 1 = d → C j 0 ≤ lo ∨ hi ≤ C j 0)
    (hlohi : lo < hi)
    (hR : ∃ R : ZMod n, C R 0 + c * C R 1 = d ∧ hi ≤ C R 0)
    (hL : ∃ L : ZMod n, C L 0 + c * C L 1 = d ∧ C L 0 ≤ lo) :
    ∃ k : ZMod n, (hi ≤ C k 0 ∧ C (k + 1) 0 ≤ lo) ∨ (hi ≤ C (k + 1) 0 ∧ C k 0 ≤ lo) := by
  classical
  by_contra h_contra;
  -- Set `jL` and `jR` as described.
  obtain ⟨R, hR₁, hR₂⟩ := hR
  obtain ⟨L, hL₁, hL₂⟩ := hL
  have : NeZero n := ⟨by omega⟩
  set jL := (L - R).val
  have hjL_pos : 1 ≤ jL := by
    by_cases hL_eq_R : L = R;
    · grind;
    · exact Nat.pos_of_ne_zero fun h => hL_eq_R <| sub_eq_zero.mp <| ZMod.val_injective n <| by aesop;
  have hjL_lt_n : jL < n := by
    exact ZMod.val_lt _
  set jR := (R - L).val
  have hjR_pos : 1 ≤ jR := by
    simp +zetaDelta at *;
    by_cases hRL : R = L;
    · grind;
    · exact Nat.pos_of_ne_zero ( by simp +decide [ sub_eq_zero, hRL ] )
  have hjR_lt_n : jR < n := by
    exact ZMod.val_lt _
  have hj_sum : jL + jR = n := by
    have h_sum : (L - R).val + (R - L).val ≡ 0 [MOD n] := by
      simp +decide [ ← ZMod.natCast_eq_natCast_iff ];
    obtain ⟨ k, hk ⟩ := Nat.modEq_zero_iff_dvd.mp h_sum;
    nlinarith [ show k = 1 by nlinarith ];
  -- Let `i` be the smallest index in `[1, jL]` such that `C (R + i).0 < hi`.
  obtain ⟨i, hi_pos, hi_lt⟩ : ∃ i : ℕ, 1 ≤ i ∧ i ≤ jL ∧ (C (R + i)).ofLp 0 < hi ∧ ∀ j : ℕ, 1 ≤ j → j < i → (C (R + j)).ofLp 0 ≥ hi := by
    have hi_exists : ∃ i : ℕ, 1 ≤ i ∧ i ≤ jL ∧ (C (R + i)).ofLp 0 < hi := by
      use jL;
      simp +zetaDelta at *;
      exact ⟨ hjL_pos, by linarith ⟩;
    exact ⟨ Nat.find hi_exists, Nat.find_spec hi_exists |>.1, Nat.find_spec hi_exists |>.2.1, Nat.find_spec hi_exists |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min hi_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec hi_exists |>.2.1 ], hj₃ ⟩ ⟩;
  -- Let `x := R + i`.
  set x := R + i
  have hx_lt_hi : (C x).ofLp 0 < hi := by
    linarith
  have hx_ge_lo : lo < (C x).ofLp 0 := by
    simp +zetaDelta at *;
    induction hi_pos <;> simp_all +decide [ ← add_assoc ]
  have hphi_x_neg : (C x).ofLp 0 + c * (C x).ofLp 1 - d < 0 := by
    exact lt_of_le_of_ne ( sub_nonpos_of_le ( hsupp x ) ) fun h => by cases hstrip x ( by linarith ) <;> linarith;
  -- Let `i'` be the smallest index in `[1, jR]` such that `C (L + i').0 > lo`.
  obtain ⟨i', hi'_pos, hi'_lt⟩ : ∃ i' : ℕ, 1 ≤ i' ∧ i' ≤ jR ∧ (C (L + i')).ofLp 0 > lo ∧ ∀ j : ℕ, 1 ≤ j → j < i' → (C (L + j)).ofLp 0 ≤ lo := by
    have hi'_exists : ∃ i' : ℕ, 1 ≤ i' ∧ i' ≤ jR ∧ (C (L + i')).ofLp 0 > lo := by
      use jR;
      simp +zetaDelta at *;
      exact ⟨ hjR_pos, by linarith ⟩;
    exact ⟨ Nat.find hi'_exists, Nat.find_spec hi'_exists |>.1, Nat.find_spec hi'_exists |>.2.1, Nat.find_spec hi'_exists |>.2.2, fun j hj₁ hj₂ => not_lt.1 fun hj₃ => Nat.find_min hi'_exists hj₂ ⟨ hj₁, by linarith [ Nat.find_spec hi'_exists |>.2.1 ], hj₃ ⟩ ⟩;
  -- Let `y := L + i'`.
  set y := L + i'
  have hy_gt_lo : (C y).ofLp 0 > lo := by
    linarith
  have hy_le_hi : (C y).ofLp 0 < hi := by
    contrapose! h_contra;
    use y - 1;
    rcases i' with ( _ | i' ) <;> simp_all +decide;
    simp +zetaDelta at *;
    by_cases hi'_pos : 1 ≤ i' <;> simp_all +decide [ add_sub_assoc ]
  have hphi_y_neg : (C y).ofLp 0 + c * (C y).ofLp 1 - d < 0 := by
    exact lt_of_le_of_ne (sub_nonpos_of_le (hsupp y)) fun h => by
      cases hstrip y (by linarith) <;> linarith
  -- Apply `chord_side` to get the inequalities for `gx` and `gy`.
  have hgxy : cross (C L - C R) (C x - C R) ≤ 0 ∧ cross (C y - C R) (C L - C R) ≤ 0 := by
    apply And.intro;
    · convert chord_side n C hconv hsconv R i ( jL - i ) hi_pos ( Nat.sub_pos_of_lt ( lt_of_le_of_ne hi_lt.1 ( by aesop_cat ) ) ) ( by omega ) using 1 ; norm_num [ x ];
      simp +zetaDelta at *;
      rw [ Nat.cast_sub hi_lt.1 ] ; norm_num [ add_assoc, ZMod.natCast_zmod_val ];
    · convert chord_side n C hconv hsconv R ( jL ) i' hjL_pos hi'_pos _ using 1;
      · simp +zetaDelta at *;
        ring_nf;
      · by_cases hi'_eq_jR : i' = jR;
        · simp +zetaDelta at *;
          simp_all +decide;
        · omega;
  unfold cross at *;
  norm_num [ EuclideanSpace.norm_eq ] at *;
  cases le_or_gt 0 c <;> nlinarith
/-
**Support line existence, secant (Case B) case.**  When no common tangent line of
the hyperbola lies above all vertices (i.e. for every contact `t ≥ 1` some vertex is
strictly above the tangent `x + 4t² y = 2t`), the polygon must poke above the
hyperbola, and the line through the side that crosses the hyperbola is the required
secant support line.  Its two hyperbola contacts `x₁ ≤ x₂` lie on that side, so
`x₁, x₂ ≥ 1` and `|x₁ - x₂| ≤ a`.
-/
theorem support_line_caseB
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i))
    (hB : ∀ t : ℝ, 1 ≤ t → ∃ i : ZMod n, 2 * t < C i 0 + 4 * t ^ 2 * C i 1) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      ∀ i : ZMod n, C i 0 + 4 * x1 * x2 * C i 1 ≤ x1 + x2 := by
  classical
  -- Let's choose the minimizer data from `caseB_minimizer n C hn hS hB`.
  obtain ⟨t, m, ht1, hm0, hsup, iR, hiR, hL, hiL⟩ := caseB_minimizer n C hn hS hB;
  obtain ⟨k, hk⟩ := caseB_adjacent n C hn hconv hsconv (4 * t ^ 2) (2 * t + m) ((2 * t + m - Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2)) / 2) ((2 * t + m + Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2)) / 2) (fun j => by
    linarith [ hsup j ]) (fun j hj => by
    contrapose! hj;
    have := hS j;
    obtain ⟨ h₁, h₂, h₃ ⟩ := this;
    nlinarith [ mul_pos hm0 h₂, mul_pos hm0 ( sub_pos.mpr ht1 ), mul_pos h₂ ( sub_pos.mpr ht1 ), Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ), Real.mul_self_sqrt ( show 0 <= ( 2 * t + m ) ^ 2 - 4 * t ^ 2 by nlinarith ) ]) (by
  linarith [ Real.sqrt_pos.mpr ( show 0 < ( 2 * t + m ) ^ 2 - 4 * t ^ 2 by nlinarith ) ]) (by
  obtain ⟨ R, hR₁, hR₂ ⟩ := iR;
  refine' ⟨ R, by linarith, _ ⟩;
  have h_sqrt : Real.sqrt ((2 * t + m) ^ 2 - 4 * t ^ 2) ≤ 2 * (C R).ofLp 0 - (2 * t + m) := by
    rw [ Real.sqrt_le_left ] <;> nlinarith [ hS R |>.1, hS R |>.2.1, hS R |>.2.2, mul_pos ( sub_pos.mpr ht1 ) ( sub_pos.mpr hm0 ) ];
  linarith) (by
  refine' ⟨ hiR, _, _ ⟩ <;> try linarith;
  rw [ le_div_iff₀ ] <;> norm_num;
  rw [ le_sub_comm, Real.sqrt_le_left ] <;> nlinarith [ sq_nonneg ( ( C hiR ).ofLp 0 - 1 ), hS hiR |>.1, hS hiR |>.2.1, hS hiR |>.2.2 ]);
  refine' ⟨ ( 2 * t + m - Real.sqrt ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ) / 2, ( 2 * t + m + Real.sqrt ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ) / 2, _, _, _, _ ⟩ <;> norm_num at *;
  · cases hk <;> nlinarith [ hS k, hS ( k + 1 ), ( hS k ) |>.1, ( hS ( k + 1 ) ) |>.1 ];
  · nlinarith [ Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ];
  · have h_dist : |(C k).ofLp 0 - (C (k + 1)).ofLp 0| ≤ a := by
      have := hca k; rw [ dist_eq_norm ] at this; norm_num [ EuclideanSpace.norm_eq ] at this ⊢; exact (by
      exact this ▸ Real.abs_le_sqrt ( by nlinarith only ));
    cases hk <;> rw [ abs_le ] at * <;> constructor <;> linarith [ Real.sqrt_nonneg ( ( 2 * t + m ) ^ 2 - 4 * t ^ 2 ) ];
  · intro i; convert hsup i using 1 <;> ring_nf;
    rw [ Real.sq_sqrt ] <;> nlinarith
/-- **Support line existence** (geometric core of the area bound).  There is a tangent
or secant line `x + 4 x₁ x₂ y = x₁ + x₂` of the hyperbola `4xy = 1` with all vertices
on its lower side, i.e. `C i 0 + 4 x₁ x₂ · C i 1 ≤ x₁ + x₂` for every vertex.  Its two
hyperbola-contact abscissae `x₁, x₂` are `≥ 1` (case A: a single tangency point
`x₁ = x₂`; case B: the two points where a side of the polygon crosses the hyperbola),
with gap at most the side length `a`.
The proof splits on whether a common tangent above all vertices exists.  Case A is
elementary; the genuine planar-geometric content is in `support_line_caseB`. -/
theorem exists_support_line
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      ∀ i : ZMod n, C i 0 + 4 * x1 * x2 * C i 1 ≤ x1 + x2 := by
  classical
  by_cases hCaseA : ∃ t : ℝ, 1 ≤ t ∧ ∀ i : ZMod n, C i 0 + 4 * t ^ 2 * C i 1 ≤ 2 * t
  · -- Case A: a common tangent line lies above every vertex; take `x₁ = x₂ = t`.
    obtain ⟨t, ht1, htle⟩ := hCaseA
    refine ⟨t, t, ht1, ht1, ?_, ?_⟩
    · rw [sub_self, abs_zero]; exact ha.le
    · intro i; have h := htle i; nlinarith [h]
  · -- Case B: no common tangent; use the secant through the crossing side.
    push Not at hCaseA
    exact support_line_caseB n C a hn ha hconv hsconv hca hS hCaseA
/-- The convex hull of the polygon lies in the triangle cut from the coordinate axes
by the support line of `exists_support_line` (`x`-intercept `x₁ + x₂`, `y`-intercept
`(x₁ + x₂)/(4 x₁ x₂)`).  This follows from `exists_support_line` together with
convexity of `tri` (`convexHull_min`). -/
theorem exists_support_triangle
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 0 < a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    ∃ x1 x2 : ℝ, 1 ≤ x1 ∧ 1 ≤ x2 ∧ |x1 - x2| ≤ a ∧
      convexHull ℝ (Set.range C) ⊆ tri (x1 + x2) ((x1 + x2) / (4 * x1 * x2)) := by
  classical
  obtain ⟨x1, x2, hx1, hx2, hdist, hline⟩ := exists_support_line n C a hn ha hconv hsconv hca hS
  refine ⟨x1, x2, hx1, hx2, hdist, ?_⟩
  have hp : (0 : ℝ) < x1 + x2 := by linarith
  have h4 : (0 : ℝ) < 4 * x1 * x2 := by positivity
  have hq : (0 : ℝ) < (x1 + x2) / (4 * x1 * x2) := by positivity
  refine convexHull_min ?_ (tri_convex _ _)
  rintro _ ⟨i, rfl⟩
  obtain ⟨hxi1, hyi1, _⟩ := hS i
  refine ⟨by linarith, le_of_lt hyi1, ?_⟩
  have hkey : C i 0 / (x1 + x2) + C i 1 / ((x1 + x2) / (4 * x1 * x2))
      = (C i 0 + 4 * x1 * x2 * C i 1) / (x1 + x2) := by
    rw [div_div_eq_mul_div, ← add_div]
    ring_nf
  rw [hkey, div_le_one hp]
  exact hline i
/-
**Edge `x`-projection bound.**  Each side of the polygon has horizontal extent at
least `√(a² - 1/16)`: both endpoints lie in the strip `0 < y < 1/4` (since
`1 < x` and `4xy < 1` give `y < 1/(4x) < 1/4`), so the vertical extent of a side is
`< 1/4`, and Pythagoras with side length `a` gives the bound.
-/
theorem edge_dx_ge
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (ha : 2 ≤ a)
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) (i : ZMod n) :
    Real.sqrt (a ^ 2 - 1 / 16) ≤ |C (i + 1) 0 - C i 0| := by
  classical
  rw [ Real.sqrt_le_iff ];
  simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
  have := hca i; rw [ Real.sqrt_eq_iff_mul_self_eq_of_pos ] at this <;> try linarith;
  have := hS i; have := hS ( i + 1 ) ; norm_num [ inS ] at *; nlinarith [ mul_pos ( sub_pos.mpr this.1 ) ( sub_pos.mpr this.2.1 ), mul_pos ( sub_pos.mpr ( hS i |>.1 ) ) ( sub_pos.mpr ( hS i |>.2.1 ) ) ] ;
/-
Reindexing a sum over `ZMod n` as a sum over `range n` starting from any base `R`:
the map `i ↦ R + i` is a bijection `Fin n ≃ ZMod n`.
-/
theorem sum_range_zmod (n : ℕ) [NeZero n] (R : ZMod n) (h : ZMod n → ℝ) :
    ∑ i ∈ Finset.range n, h (R + (i : ZMod n)) = ∑ i : ZMod n, h i := by
  classical
  rcases n with ( _ | _ | n ) <;> norm_num [ Finset.sum_range ] at *;
  · exact False.elim <| NeZero.ne 0 rfl;
  · simp +decide [ Fin.eq_zero ];
  · erw [ Finset.sum_equiv ( Equiv.addLeft R ) ] ; aesop;
    simp +decide [ ZMod, Fin.add_def ]
/-
**No interior `x`-peak (algebraic core).**  Four points `r, a, b, c` in
counter-clockwise convex position (here `a, b, c` are three further vertices with the
convex-position cross inequalities `h1`-`h4` relative to the rightmost vertex `r`) cannot
have `b` as a strict local `x`-maximum below `r`: if `a 0 < b 0`, `c 0 < b 0` and
`b 0 ≤ r 0`, the two diagonals `r–b` and `a–c` of the convex quadrilateral `r,a,b,c`
cross, and the `x`-coordinate of the crossing point is simultaneously `≥ b 0` (it lies
on segment `r–b`, both of whose endpoints have `x ≥ b 0`) and `< b 0` (it lies on
segment `a–c`, both of whose endpoints have `x < b 0`) — a contradiction.
-/
theorem no_interior_peak_alg (r a b c : EuclideanSpace ℝ (Fin 2))
    (hab : a 0 < b 0) (hcb : c 0 < b 0) (hbr : b 0 ≤ r 0)
    (h1 : cross (b - r) (a - r) ≤ 0) (h2 : 0 < cross (b - r) (c - r))
    (h3 : cross (c - a) (b - a) ≤ 0) :
    False := by
  classical
  contrapose! h1; contrapose! h2; norm_num [ cross ] at *;
  nlinarith
/-
**Cyclic unimodality of the `x`-coordinate (valley form).**  If `R` is a vertex of
maximal `x`-coordinate, then walking by `+1` from `R` the `x`-coordinate first weakly
decreases (down to the minimum) and then weakly increases (back up to the maximum):
there is a split index `k ≤ n` with `x` non-increasing on `[0,k)` and non-decreasing on
`[k,n)`.  This is the convex-position input; were there an interior local `x`-maximum
below `R`, three cyclically ordered vertices around it would violate `chord_side`.
-/
theorem x_valley (n : ℕ) [NeZero n] (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (R : ZMod n) (hR : ∀ j : ZMod n, C j 0 ≤ C R 0) :
    ∃ k : ℕ, k ≤ n ∧
      (∀ i : ℕ, i < k → C (R + ((i + 1 : ℕ) : ZMod n)) 0 ≤ C (R + (i : ZMod n)) 0) ∧
      (∀ i : ℕ, k ≤ i → i < n → C (R + (i : ZMod n)) 0 ≤ C (R + ((i + 1 : ℕ) : ZMod n)) 0) := by
  classical
  by_contra! h_contra;
  -- Let `k` be the smallest index such that `f(R+((k+1):ℕ)) > f(R+(k:ℕ))`.
  obtain ⟨k, hk⟩ : ∃ k ≤ n, (∀ i < k, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ (k = n ∨ (C (R + (k + 1 : ℕ))).ofLp 0 > (C (R + (k : ℕ))).ofLp 0) := by
    have h_exists_k : ∃ k ≤ n, (∀ i < k, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ (k = n ∨ ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0)) := by
      have h_exists_k : ∃ k ≤ n, ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) := by
        exact ⟨ n, le_rfl, fun h => by obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := h_contra n le_rfl ( fun i hi => h i ( by linarith ) ) ; linarith [ h i ( by linarith ) ] ⟩;
      obtain ⟨k, hk⟩ : ∃ k ≤ n, ¬(∀ i < k + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) ∧ ∀ j < k, (∀ i < j + 1, (C (R + (i + 1 : ℕ))).ofLp 0 ≤ (C (R + (i : ℕ))).ofLp 0) := by
        exact ⟨ Nat.find h_exists_k, Nat.find_spec h_exists_k |>.1, Nat.find_spec h_exists_k |>.2, fun j hj => by exact Classical.not_not.1 fun h => Nat.find_min h_exists_k hj ⟨ Nat.le_trans ( Nat.le_of_lt hj ) ( Nat.find_spec h_exists_k |>.1 ), h ⟩ ⟩;
      exact ⟨ k, hk.1, fun i hi => hk.2.2 i hi i ( Nat.lt_succ_self _ ), Or.inr hk.2.1 ⟩;
    grind;
  obtain ⟨j, hj⟩ : ∃ j, k ≤ j ∧ j < n ∧ (C (R + (j + 1 : ℕ))).ofLp 0 < (C (R + (j : ℕ))).ofLp 0 ∧ ∀ i, k ≤ i → i < j → (C (R + (i + 1 : ℕ))).ofLp 0 ≥ (C (R + (i : ℕ))).ofLp 0 := by
    have := Nat.find_spec ( h_contra k hk.1 hk.2.1 );
    exact ⟨ _, this.1, this.2.1, this.2.2, fun i hi₁ hi₂ => not_lt.1 fun hi₃ => Nat.find_min ( h_contra k hk.1 hk.2.1 ) hi₂ ⟨ hi₁, by linarith, hi₃ ⟩ ⟩;
  -- By `hR`, we have `f(R+k) < f(R+j)`.
  have h_lt : (C (R + (k : ℕ))).ofLp 0 < (C (R + (j : ℕ))).ofLp 0 := by
    have h_lt : ∀ i, k + 1 ≤ i → i ≤ j → (C (R + (i : ℕ))).ofLp 0 ≥ (C (R + (k + 1 : ℕ))).ofLp 0 := by
      intro i hi₁ hi₂; induction hi₁ <;> simp_all +decide [ Nat.succ_eq_add_one ] ;
      grind;
    grind;
  have h1 : cross (C (R + (j : ℕ)) - C R) (C (R + (k : ℕ)) - C R) ≤ 0 := by
    convert chord_side n C hconv _ R k ( j - k ) _ _ _ using 1;
    · simp +decide [ hj.1 ];
    · exact hsconv;
    · rcases k with ( _ | k ) <;> norm_num at *;
      exact absurd ( hk.resolve_left ( by linarith ) ) ( not_lt_of_ge ( hR _ ) );
    · exact Nat.sub_pos_of_lt ( lt_of_le_of_ne hj.1 ( by rintro rfl; linarith ) );
    · omega
  have h2 : 0 < cross (C (R + (j : ℕ)) - C R) (C (R + (j + 1 : ℕ)) - C R) := by
    convert hsconv ( R + j ) R _ _ using 1 <;> norm_num [ add_assoc ];
    · unfold cross; simp +decide [ sub_eq_iff_eq_add ] ; ring;
    · intro h; simp_all +decide [ ZMod.natCast_eq_zero_iff ] ;
      linarith [ Nat.le_of_dvd ( by linarith [ show k > 0 from Nat.pos_of_ne_zero fun h => by subst h; specialize h_contra 0; aesop ] ) h ];
    · grind +qlia
  have h3 : cross (C (R + (j + 1 : ℕ)) - C (R + (k : ℕ))) (C (R + (j : ℕ)) - C (R + (k : ℕ))) ≤ 0 := by
    convert chord_side n C hconv hsconv ( R + k ) ( j - k ) 1 _ _ _ using 1 <;> norm_num [ hj.1, hj.2.1 ];
    · ring_nf;
    · exact Nat.sub_pos_of_lt ( lt_of_le_of_ne hj.1 ( by rintro rfl; linarith ) );
    · by_cases h_eq : j = n - 1;
      · rcases n with ( _ | _ | n ) <;> simp_all +decide;
        linarith [ hR ( R + ( n + 1 ) ) ];
      · omega
  exact no_interior_peak_alg (C R) (C (R + (k : ℕ))) (C (R + (j : ℕ))) (C (R + (j + 1 : ℕ))) h_lt hj.2.2.1 (hR (R + (j : ℕ))) h1 h2 h3
/-
**Unimodality / total `x`-variation of a convex polygon.**  For a (strictly)
convex counter-clockwise polygon the sum of the absolute horizontal extents of the
sides equals twice the horizontal width `xmax - xmin`; in particular it is `≤` that.
Going around the polygon, the `x`-coordinate rises monotonically from the leftmost to
the rightmost vertex and then falls back monotonically, so each of the two arcs
contributes exactly `xmax - xmin` to the total variation.
-/
theorem two_width_ge_sum
    (n : ℕ) [NeZero n] (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hne : (Finset.univ : Finset (ZMod n)).Nonempty) :
    ∑ i : ZMod n, |C (i + 1) 0 - C i 0|
      ≤ 2 * (Finset.univ.sup' hne (fun i => C i 0) - Finset.univ.inf' hne (fun i => C i 0)) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : ZMod n, ∀ j : ZMod n, (C j).ofLp 0 ≤ (C R).ofLp 0 := by
    simpa using Finset.exists_max_image Finset.univ ( fun j => ( C j |> fun x => x.ofLp 0 ) ) hne;
  obtain ⟨ k, hk ⟩ := x_valley n C hn hconv hsconv R hR;
  -- By `sum_range_zmod`, we can reindex the sum to start from `R`.
  have h_sum_reindex : ∑ i : ZMod n, abs ((C (i + 1)).ofLp 0 - (C i).ofLp 0) = ∑ i ∈ Finset.range n, abs ((C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - (C (R + (i : ℕ) : ZMod n)).ofLp 0) := by
    rw [ ← sum_range_zmod ];
    norm_num [ add_assoc ];
    convert rfl;
  -- Split the sum into two parts: one over the range $k$ and one over the range $n-k$.
  have h_split_sum : ∑ i ∈ Finset.range n, abs ((C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - (C (R + (i : ℕ) : ZMod n)).ofLp 0) = (∑ i ∈ Finset.range k, (C (R + (i : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.range k, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0) + (∑ i ∈ Finset.Ico k n, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.Ico k n, (C (R + (i : ℕ) : ZMod n)).ofLp 0) := by
    rw [ ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_Ico_consecutive _ _ hk.1 ];
    · rw [ ← Finset.sum_range_add_sum_Ico _ hk.1 ];
      exact congrArg₂ ( · + · ) ( Finset.sum_congr rfl fun i hi => by rw [ abs_sub_comm, abs_of_nonneg ] ; linarith [ hk.2.1 i ( Finset.mem_range.mp hi ) ] ) ( by rw [ Finset.sum_congr rfl fun i hi => abs_of_nonneg ( sub_nonneg.mpr ( hk.2.2 i ( Finset.mem_Ico.mp hi |>.1 ) ( Finset.mem_Ico.mp hi |>.2 ) ) ) ] ; norm_num );
    · linarith;
  -- Apply the telescoping sum property to each part.
  have h_telescope : (∑ i ∈ Finset.range k, (C (R + (i : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.range k, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0) = (C R).ofLp 0 - (C (R + k : ZMod n)).ofLp 0 ∧ (∑ i ∈ Finset.Ico k n, (C (R + (i + 1 : ℕ) : ZMod n)).ofLp 0 - ∑ i ∈ Finset.Ico k n, (C (R + (i : ℕ) : ZMod n)).ofLp 0) = (C (R + n : ZMod n)).ofLp 0 - (C (R + k : ZMod n)).ofLp 0 := by
    constructor;
    · convert Finset.sum_range_sub' ( fun i => ( C ( R + i ) ).ofLp 0 ) k using 1 ; norm_num;
      norm_num;
    · rw [ Finset.sum_Ico_eq_sub _ hk.1, Finset.sum_Ico_eq_sub _ hk.1 ];
      have := Finset.sum_range_sub ( fun i => ( C ( R + i ) |> fun x => x.ofLp 0 ) ) n; have := Finset.sum_range_sub ( fun i => ( C ( R + i ) |> fun x => x.ofLp 0 ) ) k; norm_num [ add_assoc, Finset.sum_range_succ ] at *; linarith;
  simp_all +decide [ Finset.inf'_eq_csInf_image ];
  linarith [ show ( Finset.univ.sup' hne fun x => ( C x |> fun y => y.ofLp 0 ) ) ≥ ( C R |> fun y => y.ofLp 0 ) from Finset.le_sup' ( fun x => ( C x |> fun y => y.ofLp 0 ) ) ( Finset.mem_univ R ), show ( sInf ( Set.range fun x => ( C x |> fun y => y.ofLp 0 ) ) ) ≤ ( C ( R + k ) |> fun y => y.ofLp 0 ) from csInf_le ( Set.finite_range _ |> Set.Finite.bddBelow ) ( Set.mem_range_self _ ) ]
/-
**Large-side case.**  When the common side length is at least `2`, the area is
strictly less than `1`.  Suppose not, i.e. `1 ≤ area`.  The support triangle
(`exists_support_triangle`) gives contacts `x₁, x₂ ≥ 1` with `|x₁ - x₂| ≤ a` and
`area ≤ 1/2 + (x₁-x₂)²/(8x₁x₂)`; with `1 ≤ area` this forces `4x₁x₂ ≤ (x₁-x₂)² ≤ a²`,
hence `(x₁+x₂)² = (x₁-x₂)² + 4x₁x₂ ≤ 2a²`.  Every vertex has `x ≤ x₁+x₂` (it lies
below the support line), so the width is `xmax - xmin ≤ x₁+x₂ ≤ √2·a`.  On the other
hand, by `two_width_ge_sum` and `edge_dx_ge`,
`n·√(a²-1/16) ≤ ∑ |Δxᵢ| ≤ 2(xmax-xmin) ≤ 2√2·a`, so `3√(a²-1/16) ≤ 2√2·a`, i.e.
`a² ≤ 9/16`, contradicting `a ≥ 2`.
-/
theorem area_lt_one_of_large
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (hn : 3 ≤ n) (ha : 2 ≤ a)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hca : ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    volume (convexHull ℝ (Set.range C)) < 1 := by
  classical
  contrapose! hS;
  -- By contradiction, assume all vertices lie in `S`.
  by_contra h_all_in_S
  push Not at h_all_in_S;
  have : NeZero n := ⟨by omega⟩
  have hne : (Finset.univ : Finset (ZMod n)).Nonempty := Finset.univ_nonempty
  obtain ⟨x1, x2, hx1, hx2, hdist, hsub⟩ := exists_support_triangle n C a hn (by linarith) hconv hsconv hca h_all_in_S
  set p := x1 + x2
  set q := (x1 + x2) / (4 * x1 * x2) with hq_def
  have hp_pos : 0 < p := by
    exact add_pos_of_pos_of_nonneg ( zero_lt_one.trans_le hx1 ) ( zero_le_one.trans hx2 )
  have hq_pos : 0 < q := by
    positivity
  have h_area_bound : volume (convexHull ℝ (Set.range C)) ≤ ENNReal.ofReal (1 / 2 + (x1 - x2)^2 / (8 * x1 * x2)) := by
    refine' le_trans ( MeasureTheory.measure_mono hsub ) _;
    rw [ volume_tri p q hp_pos hq_pos ];
    grind +qlia;
  have h_sum_bound : (n : ℝ) * Real.sqrt (a^2 - 1/16) ≤ 2 * (x1 + x2) := by
    have h_sum_bound : ∑ i : ZMod n, |C (i + 1) 0 - C i 0| ≤ 2 * (x1 + x2) := by
      refine' le_trans ( two_width_ge_sum n C hn hconv hsconv hne ) _;
      gcongr;
      refine' sub_le_iff_le_add'.mpr _;
      refine' Finset.sup'_le _ _ _;
      intro i hi; have := hsub ( subset_convexHull ℝ _ <| Set.mem_range_self i ) ; simp_all +decide [ tri ] ;
      exact le_trans ( show ( C i |> fun z => z.ofLp 0 ) ≤ x1 + x2 from by have := this.2.2; rw [ div_add_div, div_le_iff₀ ] at this <;> nlinarith ) ( le_add_of_nonneg_left <| Finset.le_inf' _ _ fun x hx => by have := h_all_in_S x; exact this.1.le.trans' <| by norm_num );
    refine le_trans ?_ h_sum_bound;
    exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun i _ => edge_dx_ge n C a ha hca h_all_in_S i );
  have h_final_bound : 4 * x1 * x2 ≤ (x1 - x2)^2 := by
    have h_final_bound : 1 ≤ 1 / 2 + (x1 - x2)^2 / (8 * x1 * x2) := by
      contrapose! hS;
      exact lt_of_le_of_lt h_area_bound ( ENNReal.ofReal_lt_one.mpr hS );
    nlinarith [ mul_pos ( zero_lt_one.trans_le hx1 ) ( zero_lt_one.trans_le hx2 ), div_mul_cancel₀ ( ( x1 - x2 ) ^ 2 ) ( by positivity : ( 8 * x1 * x2 ) ≠ 0 ) ];
  have h_final_bound : (n : ℝ)^2 * (a^2 - 1/16) ≤ 8 * a^2 := by
    have h_final_bound : (n : ℝ)^2 * (a^2 - 1/16) ≤ 4 * (x1 + x2)^2 := by
      nlinarith only [ show 0 ≤ ( n : ℝ ) * Real.sqrt ( a ^ 2 - 1 / 16 ) by positivity, h_sum_bound, Real.mul_self_sqrt ( show 0 ≤ a ^ 2 - 1 / 16 by nlinarith only [ ha ] ) ];
    exact h_final_bound.trans ( by nlinarith only [ abs_le.mp hdist, ‹4 * x1 * x2 ≤ ( x1 - x2 ) ^ 2› ] );
  nlinarith [ show ( n : ℝ ) ≥ 3 by norm_cast, sq_nonneg ( a - 2 ), mul_le_mul_of_nonneg_left ( show ( n : ℝ ) ≥ 3 by norm_cast ) ( show 0 ≤ a by positivity ) ]
/-- The inner content of the theorem: a convex (ccw) polygon with congruent sides
and all vertices in `S` has area `< 1`. -/
theorem area_lt_one
    (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2))
    (hn : 3 ≤ n)
    (hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i))
    (hsconv : ∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i))
    (hcong : ∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a)
    (hS : ∀ i : ZMod n, inS (C i)) :
    volume (convexHull ℝ (Set.range C)) < 1 := by
  classical
  obtain ⟨a, ha, hca⟩ := hcong
  rcases lt_or_ge a 2 with hlt | hge
  · -- Small side: the area bound already gives `< 1`.
    obtain ⟨x1, x2, hx1, hx2, hdist, hsub⟩ :=
      exists_support_triangle n C a hn ha hconv hsconv hca hS
    have hp : 0 < x1 + x2 := by linarith
    have hq : 0 < (x1 + x2) / (4 * x1 * x2) := by positivity
    have hbound :
        volume (convexHull ℝ (Set.range C))
          ≤ ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2)) := by
      calc volume (convexHull ℝ (Set.range C))
            ≤ volume (tri (x1 + x2) ((x1 + x2) / (4 * x1 * x2))) := measure_mono hsub
        _ = ENNReal.ofReal ((x1 + x2) * ((x1 + x2) / (4 * x1 * x2)) / 2) :=
              volume_tri _ _ hp hq
        _ = ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2)) := by
              rw [← hyparea_identity x1 x2 (by linarith) (by linarith)]
              congr 1
              field_simp
              ring
    refine lt_of_le_of_lt hbound ?_
    have hxx : (1 : ℝ) ≤ x1 * x2 := by nlinarith
    have habs : (x1 - x2) ^ 2 ≤ a ^ 2 := by nlinarith [abs_nonneg (x1 - x2), sq_abs (x1 - x2)]
    have hlt1 : 1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2) < 1 := by
      have h8 : 0 < 8 * x1 * x2 := by nlinarith
      have hhalf : (x1 - x2) ^ 2 / (8 * x1 * x2) < 1 / 2 := by
        rw [div_lt_iff₀ h8]; nlinarith
      linarith
    calc ENNReal.ofReal (1 / 2 + (x1 - x2) ^ 2 / (8 * x1 * x2))
          < ENNReal.ofReal 1 := by
            exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hlt1
      _ = 1 := by simp
  · -- Large side: handled by the projection argument.
    exact area_lt_one_of_large n C a hn hge hconv hsconv hca hS
/-- **Theorem `thm:congruent`.**  There exists a planar set `S` of infinite Lebesgue
measure such that every convex polygon with congruent sides and all vertices in `S`
has area strictly less than `1`. -/
theorem thm_congruent :
    ∃ S : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet S ∧ volume S = ⊤ ∧
      ∀ (n : ℕ) (C : ZMod n → EuclideanSpace ℝ (Fin 2)),
        3 ≤ n →
        (∀ i j : ZMod n, j ≠ i → j ≠ i + 1 → 0 < cross (C (i + 1) - C i) (C j - C i)) →
        (∃ a : ℝ, 0 < a ∧ ∀ i : ZMod n, dist (C i) (C (i + 1)) = a) →
        (∀ i : ZMod n, C i ∈ S) →
        volume (convexHull ℝ (Set.range C)) < 1 := by
  classical
  refine ⟨Sset, measurableSet_Sset, volume_Sset_top, ?_⟩
  intro n C hn hsconv hcong hS
  -- Strict convexity (`hsconv`) yields the weak convexity `hconv` used internally.
  have hconv : ∀ i j : ZMod n, 0 ≤ cross (C (i + 1) - C i) (C j - C i) := by
    intro i j
    by_cases hji : j = i
    · rw [hji]
      have h0 : cross (C (i + 1) - C i) (C i - C i) = 0 := by unfold cross; simp
      rw [h0]
    · by_cases hji1 : j = i + 1
      · rw [hji1]
        have h0 : cross (C (i + 1) - C i) (C (i + 1) - C i) = 0 := by unfold cross; ring
        rw [h0]
      · exact (hsconv i j hji hji1).le
  exact area_lt_one n C hn hconv hsconv hcong hS
end Kovac
end Erdos353
