/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1127.
https://www.erdosproblems.com/forum/thread/1127

Informal authors:
- Kenneth Kunen

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1127.md
-/
import Mathlib
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Combinatorics.Matroid.Circuit

open scoped Cardinal

namespace Erdos1127

/-- The continuum hypothesis, in the universe containing `ℝ`. -/
def ContinuumHypothesis : Prop :=
  𝔠 = (ℵ_ 1 : Cardinal.{0})

/-- The correct unordered-edge interpretation of "all pairwise distances are distinct".

The inequalities exclude diagonal pairs, and the disjunction in the conclusion identifies an
edge with its reversal. -/
def HasDistinctPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- An over-strong interpretation which treats oriented pairs as distinct. -/
def HasDistinctOrientedPairDistances {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    x ≠ y → u ≠ v →
    dist x y = dist u v →
    x = u ∧ y = v

/-- A second over-strong interpretation which compares diagonal pairs as well. -/
def HasDistinctIncludingDegeneratePairs {X : Type*} [PseudoMetricSpace X]
    (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y →
    color x = color u →
    color x = color v →
    dist x y = dist u v →
    (x = u ∧ y = v) ∨ (x = v ∧ y = u)

lemma injective_of_hasDistinctOrientedPairDistances
    {X : Type*} [PseudoMetricSpace X] {color : X → ℕ}
    (h : HasDistinctOrientedPairDistances color) : Function.Injective color := by
  intro x y hxy
  by_contra hne
  have hs := h hxy hxy rfl hne (Ne.symm hne) (dist_comm x y)
  exact hne hs.1

/-- MAIN RESULT (counterexample to the oriented-pair formulation): no coloring of the real line
by natural numbers can give distinct distances to oriented nondegenerate pairs. -/
theorem erdos_1127_oriented_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctOrientedPairDistances color := by
  rintro ⟨color, hcolor⟩
  have hinj : Function.Injective color :=
    injective_of_hasDistinctOrientedPairDistances hcolor
  have hcard : 𝔠 ≤ ℵ₀ := by
    simpa only [Cardinal.mk_real, Cardinal.mk_nat] using
      Cardinal.mk_le_of_injective hinj
  exact Cardinal.aleph0_lt_continuum.2 hcard

lemma injective_of_hasDistinctIncludingDegeneratePairs
    {X : Type*} [PseudoMetricSpace X] {color : X → ℕ}
    (h : HasDistinctIncludingDegeneratePairs color) : Function.Injective color := by
  intro x y hxy
  have hs := h (x := x) (y := x) (u := y) (v := y)
    rfl hxy hxy (by simp)
  exact hs.elim And.left And.left

/-- MAIN RESULT (counterexample to allowing degenerate pairs): zero-distance loops at two
same-colored points would have to be the same unordered pair. -/
theorem erdos_1127_degenerate_pair_formulation_false :
    ¬ ∃ color : ℝ → ℕ, HasDistinctIncludingDegeneratePairs color := by
  rintro ⟨color, hcolor⟩
  have hinj : Function.Injective color :=
    injective_of_hasDistinctIncludingDegeneratePairs hcolor
  have hcard : 𝔠 ≤ ℵ₀ := by
    simpa only [Cardinal.mk_real, Cardinal.mk_nat] using
      Cardinal.mk_le_of_injective hinj
  exact Cardinal.aleph0_lt_continuum.2 hcard

/-- The exact positive statement in Problem 1127. `EuclideanSpace` is used deliberately: the
plain function type carries the sup metric rather than the Euclidean `ℓ²` metric. -/
def PositiveAnswer : Prop :=
  ∀ n : ℕ, ∃ color : EuclideanSpace ℝ (Fin n) → ℕ,
    HasDistinctPairDistances color

/-! ## The two algebraic obstructions

For a monochromatic set, two different nondegenerate unordered pairs with the same distance
have either three or four vertices.  The three-vertex case is an isosceles triangle (the zero
set of Schmerl's polynomial `P₃`), and the four-vertex case consists of two disjoint pairs (the
zero set of `P₄`).  The following definitions use distances rather than squared distances, which
is equivalent over `ℝ` and makes the final combinatorial reduction independent of coordinates.
-/

/-- A coloring avoids monochromatic isosceles triangles on three distinct vertices. -/
def AvoidsP3 {X : Type*} [PseudoMetricSpace X] (color : X → ℕ) : Prop :=
  ∀ ⦃x y z : X⦄,
    color x = color y → color x = color z →
    x ≠ y → x ≠ z → y ≠ z →
    dist x y ≠ dist x z

/-- A coloring avoids equal distances between two monochromatic disjoint pairs. -/
def AvoidsP4 {X : Type*} [PseudoMetricSpace X] (color : X → ℕ) : Prop :=
  ∀ ⦃x y u v : X⦄,
    color x = color y → color x = color u → color x = color v →
    x ≠ y → u ≠ v → x ≠ u → x ≠ v → y ≠ u → y ≠ v →
    dist x y ≠ dist u v

/-- Avoiding the `P₃` and `P₄` zero-loci is exactly what is needed for all nondegenerate
unordered-pair distances in every color class to be distinct. -/
theorem hasDistinctPairDistances_iff_avoidsP3_and_avoidsP4
    {X : Type*} [PseudoMetricSpace X] {color : X → ℕ} :
    HasDistinctPairDistances color ↔ AvoidsP3 color ∧ AvoidsP4 color := by
  constructor
  · intro h
    constructor
    · intro x y z hxy hxz hnxy hnxz hnyz heq
      rcases h hxy rfl hxz hnxy hnxz heq with hsame | hreverse
      · exact hnyz hsame.2
      · exact hnxz hreverse.1
    · intro x y u v hxy hxu hxv hnxy hnuv hnxu hnxv hnyu hnyv heq
      rcases h hxy hxu hxv hnxy hnuv heq with hsame | hreverse
      · exact hnxu hsame.1
      · exact hnxv hreverse.1
  · rintro ⟨h3, h4⟩ x y u v hxy hxu hxv hnxy hnuv heq
    by_cases hxu' : x = u
    · left
      refine ⟨hxu', ?_⟩
      by_contra hyv
      subst u
      exact h3 hxy hxv hnxy hnuv hyv heq
    by_cases hxv' : x = v
    · right
      refine ⟨hxv', ?_⟩
      by_contra hyu
      subst v
      apply h3 hxy hxu hnxy hxu' hyu
      simpa only [dist_comm x u] using heq
    by_cases hyu : y = u
    · exfalso
      subst u
      apply h3 hxy.symm (hxy.symm.trans hxv) (Ne.symm hnxy)
        hnuv hxv'
      simpa only [dist_comm y x] using heq
    by_cases hyv : y = v
    · exfalso
      subst v
      apply h3 hxy.symm (hxy.symm.trans hxu) (Ne.symm hnxy)
        hyu hxu'
      simpa only [dist_comm y x, dist_comm y u] using heq
    · exfalso
      exact (h4 hxy hxu hxv hnxy hnuv hxu' hxv' hyu hyv) heq

/-! Schmerl's master-coloring theorem is stated for polynomial zero-sets.  Here are the exact
coordinate polynomials and the elementary one-variable collapse witnesses needed in its
hypotheses. -/

/-- Squared Euclidean distance, written as a polynomial in the coordinates. -/
def squaredDistance {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, (x i - y i) ^ 2

theorem squaredDistance_eq_dist_sq {n : ℕ}
    (x y : EuclideanSpace ℝ (Fin n)) :
    squaredDistance x y = dist x y ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [squaredDistance, Real.dist_eq, sq_abs]

theorem squaredDistance_ne_zero {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)} (hxy : x ≠ y) :
    squaredDistance x y ≠ 0 := by
  rw [squaredDistance_eq_dist_sq]
  exact pow_ne_zero 2 (dist_ne_zero.mpr hxy)

/-- The shared-endpoint equal-distance polynomial `P₃`. -/
def distancePolynomial3 {n : ℕ}
    (x y z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  squaredDistance x y - squaredDistance x z

/-- The disjoint-pair equal-distance polynomial `P₄`. -/
def distancePolynomial4 {n : ℕ}
    (x y u v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  squaredDistance x y - squaredDistance u v

/-- A strong, purely set-theoretic version of one-avoidability for a ternary relation.  It is
stronger than Schmerl's definition, which only quantifies over definable coordinatewise-injective
maps on an interval. -/
def StrongOneAvoidable3 {X : Type*} (p : X → X → X → ℝ) : Prop :=
  ∀ (g : ℝ → X), Function.Injective g →
    ∀ e₀ e₁ e₂ : ℝ, e₀ ≠ e₁ → e₀ ≠ e₂ → e₁ ≠ e₂ →
      ∃ α : ℝ → ℝ, p (g (α e₀)) (g (α e₁)) (g (α e₂)) ≠ 0

/-- The corresponding strong one-avoidability property for a quaternary relation. -/
def StrongOneAvoidable4 {X : Type*} (p : X → X → X → X → ℝ) : Prop :=
  ∀ (g : ℝ → X), Function.Injective g →
    ∀ e₀ e₁ e₂ e₃ : ℝ,
      e₀ ≠ e₁ → e₀ ≠ e₂ → e₀ ≠ e₃ → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ →
      ∃ α : ℝ → ℝ,
        p (g (α e₀)) (g (α e₁)) (g (α e₂)) (g (α e₃)) ≠ 0

/-- `P₃` is one-avoidable: collapse its first two inputs to `g 0` and send the third
to `g 1`. -/
theorem distancePolynomial3_strongOneAvoidable {n : ℕ} :
    StrongOneAvoidable3 (distancePolynomial3 (n := n)) := by
  intro g hg e₀ e₁ e₂ he₀₁ he₀₂ he₁₂
  let α : ℝ → ℝ := fun t ↦ if t = e₂ then 1 else 0
  refine ⟨α, ?_⟩
  have h0 : g 0 ≠ g 1 := hg.ne zero_ne_one
  simp only [distancePolynomial3, α, if_neg he₀₂, if_neg he₁₂, if_pos rfl,
    squaredDistance_eq_dist_sq, dist_self, ne_eq, OfNat.ofNat]
  norm_num only [zero_pow, zero_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (dist_ne_zero.mpr h0))

/-- `P₄` is one-avoidable: retain one nondegenerate pair and collapse the other pair. -/
theorem distancePolynomial4_strongOneAvoidable {n : ℕ} :
    StrongOneAvoidable4 (distancePolynomial4 (n := n)) := by
  intro g hg e₀ e₁ e₂ e₃ he₀₁ he₀₂ he₀₃ he₁₂ he₁₃ he₂₃
  let α : ℝ → ℝ := fun t ↦ if t = e₁ then 1 else 0
  refine ⟨α, ?_⟩
  have h0 : g 0 ≠ g 1 := hg.ne zero_ne_one
  simp only [distancePolynomial4, α, if_neg he₀₁, if_pos rfl,
    if_neg he₁₂.symm, if_neg he₁₃.symm, squaredDistance_eq_dist_sq,
    dist_self, ne_eq, OfNat.ofNat]
  norm_num only [zero_pow, sub_zero]
  exact pow_ne_zero 2 (dist_ne_zero.mpr h0)

theorem distancePolynomial3_eq_zero_iff {n : ℕ}
    (x y z : EuclideanSpace ℝ (Fin n)) :
    distancePolynomial3 x y z = 0 ↔ dist x y = dist x z := by
  rw [distancePolynomial3, sub_eq_zero, squaredDistance_eq_dist_sq,
    squaredDistance_eq_dist_sq, sq_eq_sq₀ (dist_nonneg) (dist_nonneg)]

theorem distancePolynomial4_eq_zero_iff {n : ℕ}
    (x y u v : EuclideanSpace ℝ (Fin n)) :
    distancePolynomial4 x y u v = 0 ↔ dist x y = dist u v := by
  rw [distancePolynomial4, sub_eq_zero, squaredDistance_eq_dist_sq,
    squaredDistance_eq_dist_sq, sq_eq_sq₀ (dist_nonneg) (dist_nonneg)]

/-- Polynomial formulation of avoiding the three-vertex obstruction. -/
def AvoidsDistancePolynomial3 {n : ℕ}
    (color : EuclideanSpace ℝ (Fin n) → ℕ) : Prop :=
  ∀ ⦃x y z : EuclideanSpace ℝ (Fin n)⦄,
    color x = color y → color x = color z →
    x ≠ y → x ≠ z → y ≠ z →
    distancePolynomial3 x y z ≠ 0

/-- Polynomial formulation of avoiding the four-vertex obstruction. -/
def AvoidsDistancePolynomial4 {n : ℕ}
    (color : EuclideanSpace ℝ (Fin n) → ℕ) : Prop :=
  ∀ ⦃x y u v : EuclideanSpace ℝ (Fin n)⦄,
    color x = color y → color x = color u → color x = color v →
    x ≠ y → u ≠ v → x ≠ u → x ≠ v → y ≠ u → y ≠ v →
    distancePolynomial4 x y u v ≠ 0

theorem avoidsDistancePolynomial3_iff_avoidsP3 {n : ℕ}
    {color : EuclideanSpace ℝ (Fin n) → ℕ} :
    AvoidsDistancePolynomial3 color ↔ AvoidsP3 color := by
  constructor
  · intro h x y z hxy hxz hnxy hnxz hnyz heq
    exact h hxy hxz hnxy hnxz hnyz ((distancePolynomial3_eq_zero_iff x y z).mpr heq)
  · intro h x y z hxy hxz hnxy hnxz hnyz hzero
    exact h hxy hxz hnxy hnxz hnyz ((distancePolynomial3_eq_zero_iff x y z).mp hzero)

theorem avoidsDistancePolynomial4_iff_avoidsP4 {n : ℕ}
    {color : EuclideanSpace ℝ (Fin n) → ℕ} :
    AvoidsDistancePolynomial4 color ↔ AvoidsP4 color := by
  constructor
  · intro h x y u v hxy hxu hxv hnxy hnuv hnxu hnxv hnyu hnyv heq
    exact h hxy hxu hxv hnxy hnuv hnxu hnxv hnyu hnyv
      ((distancePolynomial4_eq_zero_iff x y u v).mpr heq)
  · intro h x y u v hxy hxu hxv hnxy hnuv hnxu hnxv hnyu hnyv hzero
    exact h hxy hxu hxv hnxy hnuv hnxu hnxv hnyu hnyv
      ((distancePolynomial4_eq_zero_iff x y u v).mp hzero)

/-- The exact master-coloring conclusion required from the Schmerl--Kunen construction. -/
def HasDistancePolynomialMasterColoring (n : ℕ) : Prop :=
  ∃ color : EuclideanSpace ℝ (Fin n) → ℕ,
    AvoidsDistancePolynomial3 color ∧ AvoidsDistancePolynomial4 color

theorem hasDistancePolynomialMasterColoring_iff (n : ℕ) :
    HasDistancePolynomialMasterColoring n ↔
      ∃ color : EuclideanSpace ℝ (Fin n) → ℕ, HasDistinctPairDistances color := by
  constructor
  · rintro ⟨color, h3, h4⟩
    refine ⟨color, (hasDistinctPairDistances_iff_avoidsP3_and_avoidsP4).mpr ?_⟩
    exact ⟨avoidsDistancePolynomial3_iff_avoidsP3.mp h3,
      avoidsDistancePolynomial4_iff_avoidsP4.mp h4⟩
  · rintro ⟨color, hcolor⟩
    have h := (hasDistinctPairDistances_iff_avoidsP3_and_avoidsP4).mp hcolor
    exact ⟨color, avoidsDistancePolynomial3_iff_avoidsP3.mpr h.1,
      avoidsDistancePolynomial4_iff_avoidsP4.mpr h.2⟩

theorem positiveAnswer_iff_distancePolynomialMasterColorings :
    PositiveAnswer ↔ ∀ n : ℕ, HasDistancePolynomialMasterColoring n := by
  simp only [PositiveAnswer, hasDistancePolynomialMasterColoring_iff]

theorem distancePolynomialMasterColoring_zero :
    HasDistancePolynomialMasterColoring 0 := by
  rw [hasDistancePolynomialMasterColoring_iff]
  refine ⟨fun _ ↦ 0, ?_⟩
  intro x y u v hxy hxu hxv hnxy
  exact (hnxy (Subsingleton.elim x y)).elim

/-! Mathlib currently does not install an `IsRealClosed ℝ` instance.  The next three declarations
derive the proposition from its ordered-polynomial API.  This is one of the field-theoretic inputs
to the transcendence-support construction in Schmerl's proof. -/

private theorem nonnegative_real_isSquare {x : ℝ} (hx : 0 ≤ x) : IsSquare x := by
  exact ⟨Real.sqrt x, (Real.mul_self_sqrt hx).symm⟩

private theorem odd_degree_real_polynomial_has_root {f : Polynomial ℝ}
    (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  by_contra hroot
  push Not at hroot
  have hroots_lt (x : ℝ) : ∀ y, f.IsRoot y → y < x := by
    intro y hy
    exact (hroot y hy).elim
  have hlt_roots (x : ℝ) : ∀ y, f.IsRoot y → x < y := by
    intro y hy
    exact (hroot y hy).elim
  rcases le_total 0 f.leadingCoeff with hlc | hlc
  · have hpos : 0 < f.eval 0 :=
      Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg (hroots_lt 0) hlc
    have hneg : 0 < Int.negOnePow f.natDegree * f.eval 0 :=
      Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
        (hlt_roots 0) hlc
    rw [Int.negOnePow_odd _ ((Int.odd_coe_nat _).mpr hf)] at hneg
    norm_num at hneg
    exact lt_asymm hpos hneg
  · have hneg : f.eval 0 < 0 :=
      Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos (hroots_lt 0) hlc
    have hpos : Int.negOnePow f.natDegree * f.eval 0 < 0 :=
      Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos
        (hlt_roots 0) hlc
    rw [Int.negOnePow_odd _ ((Int.odd_coe_nat _).mpr hf)] at hpos
    norm_num at hpos
    exact lt_asymm hneg hpos

/-- The real numbers satisfy the algebraic definition of a real-closed field. -/
theorem real_isRealClosed : IsRealClosed ℝ :=
  IsRealClosed.of_linearOrderedField
    (fun {_} hx ↦ nonnegative_real_isSquare hx)
    (fun {_} hf ↦ odd_degree_real_polynomial_has_root hf)

/-- The field of real numbers algebraic over `ℚ`, used as the countable coefficient field in
the transcendence-support construction. -/
noncomputable abbrev RealAlgebraic : Type := algebraicClosure ℚ ℝ

noncomputable instance : Algebra.IsAlgebraic ℚ RealAlgebraic :=
  algebraicClosure.isAlgebraic ℚ ℝ

noncomputable instance : Countable RealAlgebraic := by
  let e : RealAlgebraic ≃ {x : ℝ // IsAlgebraic ℚ x} :=
    Equiv.subtypeEquiv (Equiv.refl ℝ) (fun _ ↦ mem_algebraicClosure_iff)
  have hc : Countable {x : ℝ // IsAlgebraic ℚ x} := Algebraic.countable ℚ ℝ
  exact Countable.of_equiv {x : ℝ // IsAlgebraic ℚ x} e.symm

/-! ### A one-variable algebraic-analytic specialization lemma

The substitution step in Schmerl's proof ultimately rests on the following elementary fact.
An analytic germ algebraic over `RealAlgebraic(X)` cannot vanish at a parameter transcendental
over `RealAlgebraic` unless the germ is identically zero.  We prove this directly, without any
semialgebraic or quantifier-elimination API: choose an algebraic relation of minimal degree in
the germ, evaluate its constant coefficient at the transcendental parameter, factor out `X`,
and use the isolated-zero theorem for analytic functions.
-/

private noncomputable def evalAlgebraicBivariate
    (P : Polynomial (Polynomial RealAlgebraic)) (x y : ℝ) : ℝ :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap RealAlgebraic ℝ) x) y

private lemma analyticAt_evalAlgebraicBivariate
    (P : Polynomial (Polynomial RealAlgebraic)) {h : ℝ → ℝ} {t : ℝ}
    (hh : AnalyticAt ℝ h t) :
    AnalyticAt ℝ (fun x ↦ evalAlgebraicBivariate P x (h x)) t := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun x ↦ evalAlgebraicBivariate (p + q) x (h x)) =
          (fun x ↦ evalAlgebraicBivariate p x (h x) +
            evalAlgebraicBivariate q x (h x)) by
        funext x
        simp [evalAlgebraicBivariate]]
      exact (hp.add hq).congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  | monomial n q =>
      have hq : AnalyticAt ℝ
          (fun x : ℝ ↦ q.eval₂ (algebraMap RealAlgebraic ℝ) x) t := by
        have hpoly : AnalyticAt ℝ
            (fun x : ℝ ↦ (q.map (algebraMap RealAlgebraic ℝ)).eval x) t :=
          (AnalyticOnNhd.eval_polynomial
            (q.map (algebraMap RealAlgebraic ℝ))) t (by simp)
        simpa only [Polynomial.eval_map] using hpoly
      rw [show (fun x ↦
          evalAlgebraicBivariate (Polynomial.monomial n q) x (h x)) =
          (fun x ↦ q.eval₂ (algebraMap RealAlgebraic ℝ) x * h x ^ n) by
        funext x
        simp [evalAlgebraicBivariate]]
      exact (hq.mul (hh.pow n)).congr (Filter.Eventually.of_forall fun _ ↦ rfl)

private def IsAlgebraicAnalyticAt (h : ℝ → ℝ) (t : ℝ) : Prop :=
  AnalyticAt ℝ h t ∧
    ∃ P : Polynomial (Polynomial RealAlgebraic), P ≠ 0 ∧
      ∀ᶠ x in nhds t, evalAlgebraicBivariate P x (h x) = 0

private theorem algebraicAnalytic_zero_at_transcendental
    {h : ℝ → ℝ} {t : ℝ} (ht : Transcendental RealAlgebraic t)
    (hh : IsAlgebraicAnalyticAt h t) (hzero : h t = 0) :
    ∀ᶠ x in nhds t, h x = 0 := by
  classical
  let Good : ℕ → Prop := fun d ↦
    ∃ P : Polynomial (Polynomial RealAlgebraic), P ≠ 0 ∧ P.natDegree = d ∧
      ∀ᶠ x in nhds t, evalAlgebraicBivariate P x (h x) = 0
  have hGood : ∃ d, Good d := by
    obtain ⟨P, hP, hrel⟩ := hh.2
    exact ⟨P.natDegree, P, hP, rfl, hrel⟩
  let d := Nat.find hGood
  obtain ⟨P, hPne, hPdeg, hPrel⟩ := Nat.find_spec hGood
  have hconstEval :
      (P.coeff 0).eval₂ (algebraMap RealAlgebraic ℝ) t = 0 := by
    have hPt := hPrel.self_of_nhds
    rw [hzero] at hPt
    simpa [evalAlgebraicBivariate] using hPt
  have hconst : P.coeff 0 = 0 := by
    have hi : Function.Injective
        (Polynomial.aeval (R := RealAlgebraic) t : Polynomial RealAlgebraic →+* ℝ) :=
      transcendental_iff_injective.mp ht
    apply hi
    simpa [Polynomial.aeval_def] using hconstEval
  obtain ⟨Q, hPQ⟩ := Polynomial.X_dvd_iff.mpr hconst
  have hQne : Q ≠ 0 := by
    intro hQ
    apply hPne
    simp [hPQ, hQ]
  rcases hh.1.eventually_eq_zero_or_eventually_ne_zero with hlocal | hpunctured
  · exact hlocal
  · have hQpunctured : ∀ᶠ x in nhdsWithin t {t}ᶜ,
        evalAlgebraicBivariate Q x (h x) = 0 := by
      filter_upwards [hPrel.filter_mono nhdsWithin_le_nhds, hpunctured] with x hx hxh
      rw [hPQ] at hx
      have hx' : h x * evalAlgebraicBivariate Q x (h x) = 0 := by
        simpa [evalAlgebraicBivariate] using hx
      exact (mul_eq_zero.mp hx').resolve_left hxh
    have hQfrequent : ∃ᶠ x in nhdsWithin t {t}ᶜ,
        evalAlgebraicBivariate Q x (h x) = 0 := hQpunctured.frequently
    have hQrel : ∀ᶠ x in nhds t, evalAlgebraicBivariate Q x (h x) = 0 :=
      (analyticAt_evalAlgebraicBivariate Q hh.1).frequently_zero_iff_eventually_zero.mp
        hQfrequent
    have hQgood : Good Q.natDegree := ⟨Q, hQne, rfl, hQrel⟩
    have hminimal : d ≤ Q.natDegree := Nat.find_min' hGood hQgood
    have hdegree : d = Q.natDegree + 1 := by
      change Nat.find hGood = Q.natDegree + 1
      rw [← hPdeg, hPQ,
        Polynomial.natDegree_mul Polynomial.X_ne_zero hQne]
      simp [Nat.add_comm]
    omega

private noncomputable def evalBivariateOver
    {K : Type*} [CommRing K] [Algebra K ℝ]
    (P : Polynomial (Polynomial K)) (x y : ℝ) : ℝ :=
  P.eval₂ (Polynomial.eval₂RingHom (algebraMap K ℝ) x) y

/-! Algebraic analytic germs are closed under the ring operations needed below.  The useful
base ring is `K[X]`: it acts on germs at `t` by evaluating `X` at the identity germ.  Mathlib's
general closure theorems for algebraic elements then do the elimination which, on paper, is
usually expressed with resultants. -/

private noncomputable def polynomialToGerm
    (K : Type*) [Field K] [Algebra K ℝ] (t : ℝ) :
    Polynomial K →+* Filter.Germ (nhds t) ℝ where
  toFun q := (fun x : ℝ ↦ q.eval₂ (algebraMap K ℝ) x)
  map_one' := by
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (by simp)
  map_mul' p q := by
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (by simp)
  map_zero' := by
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (by simp)
  map_add' p q := by
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (by simp)

private noncomputable def polynomialGermAlgebra
    (K : Type*) [Field K] [Algebra K ℝ] (t : ℝ) :
    Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
  (polynomialToGerm K t).toAlgebra

private lemma evalBivariateOver_germ
    {K : Type*} [Field K] [Algebra K ℝ]
    (P : Polynomial (Polynomial K)) (h : ℝ → ℝ) (t : ℝ) :
    P.eval₂ (polynomialToGerm K t)
        (h : Filter.Germ (nhds t) ℝ) =
      ((fun x ↦ evalBivariateOver P x (h x)) :
        Filter.Germ (nhds t) ℝ) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [Polynomial.eval₂_add, hp, hq]
      change
        ((fun x ↦ evalBivariateOver p x (h x) +
            evalBivariateOver q x (h x)) : Filter.Germ (nhds t) ℝ) = _
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (by simp [evalBivariateOver])
  | monomial n q =>
      rw [Polynomial.eval₂_monomial]
      change
        ((fun x : ℝ ↦ q.eval₂ (algebraMap K ℝ) x) :
            Filter.Germ (nhds t) ℝ) *
          (h : Filter.Germ (nhds t) ℝ) ^ n = _
      change
        ((fun x ↦ q.eval₂ (algebraMap K ℝ) x * h x ^ n) :
            Filter.Germ (nhds t) ℝ) = _
      apply Filter.Germ.coe_eq.mpr
      exact Filter.Eventually.of_forall (by simp [evalBivariateOver])

private lemma analyticAt_evalBivariateOver
    {K : Type*} [CommRing K] [Algebra K ℝ]
    (P : Polynomial (Polynomial K)) {h : ℝ → ℝ} {t : ℝ}
    (hh : AnalyticAt ℝ h t) :
    AnalyticAt ℝ (fun x ↦ evalBivariateOver P x (h x)) t := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun x ↦ evalBivariateOver (p + q) x (h x)) =
          (fun x ↦ evalBivariateOver p x (h x) +
            evalBivariateOver q x (h x)) by
        funext x
        simp [evalBivariateOver]]
      exact (hp.add hq).congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  | monomial n q =>
      have hq : AnalyticAt ℝ
          (fun x : ℝ ↦ q.eval₂ (algebraMap K ℝ) x) t := by
        have hpoly : AnalyticAt ℝ
            (fun x : ℝ ↦ (q.map (algebraMap K ℝ)).eval x) t :=
          (AnalyticOnNhd.eval_polynomial (q.map (algebraMap K ℝ))) t (by simp)
        simpa only [Polynomial.eval_map] using hpoly
      rw [show (fun x ↦
          evalBivariateOver (Polynomial.monomial n q) x (h x)) =
          (fun x ↦ q.eval₂ (algebraMap K ℝ) x * h x ^ n) by
        funext x
        simp [evalBivariateOver]]
      exact (hq.mul (hh.pow n)).congr (Filter.Eventually.of_forall fun _ ↦ rfl)

private def IsAlgebraicAnalyticAtOver
    (K : Type*) [CommRing K] [Algebra K ℝ] (h : ℝ → ℝ) (t : ℝ) : Prop :=
  AnalyticAt ℝ h t ∧
    ∃ P : Polynomial (Polynomial K), P ≠ 0 ∧
      ∀ᶠ x in nhds t, evalBivariateOver P x (h x) = 0

private theorem algebraicGerm_of_isAlgebraicAnalyticAtOver
    {K : Type*} [Field K] [Algebra K ℝ]
    {h : ℝ → ℝ} {t : ℝ} (hh : IsAlgebraicAnalyticAtOver K h t) :
    letI : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
      polynomialGermAlgebra K t
    IsAlgebraic (Polynomial K) (h : Filter.Germ (nhds t) ℝ) := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  obtain ⟨P, hP, hrel⟩ := hh.2
  refine ⟨P, hP, ?_⟩
  rw [Polynomial.aeval_def]
  change P.eval₂ (polynomialToGerm K t)
      (h : Filter.Germ (nhds t) ℝ) = 0
  rw [evalBivariateOver_germ]
  exact Filter.Germ.coe_eq.mpr hrel

private theorem isAlgebraicAnalyticAtOver_of_algebraicGerm
    {K : Type*} [Field K] [Algebra K ℝ]
    {h : ℝ → ℝ} {t : ℝ} (han : AnalyticAt ℝ h t)
    (hg : letI : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
        polynomialGermAlgebra K t
      IsAlgebraic (Polynomial K) (h : Filter.Germ (nhds t) ℝ)) :
    IsAlgebraicAnalyticAtOver K h t := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  obtain ⟨P, hP, hrel⟩ := hg
  refine ⟨han, P, hP, ?_⟩
  rw [Polynomial.aeval_def] at hrel
  change P.eval₂ (polynomialToGerm K t)
      (h : Filter.Germ (nhds t) ℝ) = 0 at hrel
  rw [evalBivariateOver_germ] at hrel
  exact Filter.Germ.coe_eq.mp hrel

private theorem IsAlgebraicAnalyticAtOver.add
    {K : Type*} [Field K] [Algebra K ℝ]
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t)
    (hg : IsAlgebraicAnalyticAtOver K g t) :
    IsAlgebraicAnalyticAtOver K (fun x ↦ f x + g x) t := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  apply isAlgebraicAnalyticAtOver_of_algebraicGerm (hf.1.add hg.1)
  simpa only [Filter.Germ.coe_add] using
    (algebraicGerm_of_isAlgebraicAnalyticAtOver hf).add
      (algebraicGerm_of_isAlgebraicAnalyticAtOver hg)

private theorem IsAlgebraicAnalyticAtOver.mul
    {K : Type*} [Field K] [Algebra K ℝ]
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t)
    (hg : IsAlgebraicAnalyticAtOver K g t) :
    IsAlgebraicAnalyticAtOver K (fun x ↦ f x * g x) t := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  apply isAlgebraicAnalyticAtOver_of_algebraicGerm (hf.1.mul hg.1)
  simpa only [Filter.Germ.coe_mul] using
    (algebraicGerm_of_isAlgebraicAnalyticAtOver hf).mul
      (algebraicGerm_of_isAlgebraicAnalyticAtOver hg)

private theorem IsAlgebraicAnalyticAtOver.neg
    {K : Type*} [Field K] [Algebra K ℝ]
    {f : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t) :
    IsAlgebraicAnalyticAtOver K (fun x ↦ -f x) t := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  apply isAlgebraicAnalyticAtOver_of_algebraicGerm hf.1.neg
  simpa only [Filter.Germ.coe_neg] using
    (algebraicGerm_of_isAlgebraicAnalyticAtOver hf).neg

private theorem IsAlgebraicAnalyticAtOver.sub
    {K : Type*} [Field K] [Algebra K ℝ]
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t)
    (hg : IsAlgebraicAnalyticAtOver K g t) :
    IsAlgebraicAnalyticAtOver K (fun x ↦ f x - g x) t := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

private theorem IsAlgebraicAnalyticAtOver.pow
    {K : Type*} [Field K] [Algebra K ℝ]
    {f : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t) (m : ℕ) :
    IsAlgebraicAnalyticAtOver K (fun x ↦ f x ^ m) t := by
  let : Algebra (Polynomial K) (Filter.Germ (nhds t) ℝ) :=
    polynomialGermAlgebra K t
  apply isAlgebraicAnalyticAtOver_of_algebraicGerm (hf.1.pow m)
  simpa only [Filter.Germ.coe_pow] using
    (algebraicGerm_of_isAlgebraicAnalyticAtOver hf).pow m

private theorem isAlgebraicAnalyticAtOver_const
    {K : Type*} [Field K] [Algebra K ℝ] {y : ℝ} {t : ℝ}
    (hy : IsAlgebraic K y) :
    IsAlgebraicAnalyticAtOver K (fun _ : ℝ ↦ y) t := by
  obtain ⟨p, hp, hpy⟩ := hy
  let P : Polynomial (Polynomial K) := p.map Polynomial.C
  have hP : P ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff Polynomial.C_injective).mpr hp
  refine ⟨analyticAt_const, P, hP, ?_⟩
  exact Filter.Eventually.of_forall fun x ↦ by
    change (p.map Polynomial.C).eval₂
        (Polynomial.eval₂RingHom (algebraMap K ℝ) x) y = 0
    rw [Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hpy
    have hcomp :
        (Polynomial.eval₂RingHom (algebraMap K ℝ) x).comp Polynomial.C =
          algebraMap K ℝ := by
      ext a
      simp
    rw [hcomp]
    exact hpy

private theorem IsAlgebraicAnalyticAtOver.congr
    {K : Type*} [CommRing K] [Algebra K ℝ]
    {f g : ℝ → ℝ} {t : ℝ}
    (hf : IsAlgebraicAnalyticAtOver K f t) (hfg : f =ᶠ[nhds t] g) :
    IsAlgebraicAnalyticAtOver K g t := by
  refine ⟨hf.1.congr hfg, ?_⟩
  obtain ⟨P, hP, hrel⟩ := hf.2
  refine ⟨P, hP, ?_⟩
  filter_upwards [hrel, hfg] with x hx heq
  rwa [← heq]

private theorem algebraicAnalytic_zero_at_transcendental_over
    {K : Type*} [Field K] [Algebra K ℝ]
    {h : ℝ → ℝ} {t : ℝ} (ht : Transcendental K t)
    (hh : IsAlgebraicAnalyticAtOver K h t) (hzero : h t = 0) :
    ∀ᶠ x in nhds t, h x = 0 := by
  classical
  let Good : ℕ → Prop := fun d ↦
    ∃ P : Polynomial (Polynomial K), P ≠ 0 ∧ P.natDegree = d ∧
      ∀ᶠ x in nhds t, evalBivariateOver P x (h x) = 0
  have hGood : ∃ d, Good d := by
    obtain ⟨P, hP, hrel⟩ := hh.2
    exact ⟨P.natDegree, P, hP, rfl, hrel⟩
  let d := Nat.find hGood
  obtain ⟨P, hPne, hPdeg, hPrel⟩ := Nat.find_spec hGood
  have hconstEval : (P.coeff 0).eval₂ (algebraMap K ℝ) t = 0 := by
    have hPt := hPrel.self_of_nhds
    rw [hzero] at hPt
    simpa [evalBivariateOver] using hPt
  have hconst : P.coeff 0 = 0 := by
    have hi : Function.Injective
        (Polynomial.aeval (R := K) t : Polynomial K →+* ℝ) :=
      transcendental_iff_injective.mp ht
    apply hi
    simpa [Polynomial.aeval_def] using hconstEval
  obtain ⟨Q, hPQ⟩ := Polynomial.X_dvd_iff.mpr hconst
  have hQne : Q ≠ 0 := by
    intro hQ
    apply hPne
    simp [hPQ, hQ]
  rcases hh.1.eventually_eq_zero_or_eventually_ne_zero with hlocal | hpunctured
  · exact hlocal
  · have hQpunctured : ∀ᶠ x in nhdsWithin t {t}ᶜ,
        evalBivariateOver Q x (h x) = 0 := by
      filter_upwards [hPrel.filter_mono nhdsWithin_le_nhds, hpunctured] with x hx hxh
      rw [hPQ] at hx
      have hx' : h x * evalBivariateOver Q x (h x) = 0 := by
        simpa [evalBivariateOver] using hx
      exact (mul_eq_zero.mp hx').resolve_left hxh
    have hQfrequent : ∃ᶠ x in nhdsWithin t {t}ᶜ,
        evalBivariateOver Q x (h x) = 0 := hQpunctured.frequently
    have hQrel : ∀ᶠ x in nhds t, evalBivariateOver Q x (h x) = 0 :=
      (analyticAt_evalBivariateOver Q hh.1).frequently_zero_iff_eventually_zero.mp
        hQfrequent
    have hQgood : Good Q.natDegree := ⟨Q, hQne, rfl, hQrel⟩
    have hminimal : d ≤ Q.natDegree := Nat.find_min' hGood hQgood
    have hdegree : d = Q.natDegree + 1 := by
      change Nat.find hGood = Q.natDegree + 1
      rw [← hPdeg, hPQ,
        Polynomial.natDegree_mul Polynomial.X_ne_zero hQne]
      simp [Nat.add_comm]
    omega

private theorem realAlgebraic_sqrt_isAlgebraic (x : RealAlgebraic) (hx : 0 ≤ x) :
    IsAlgebraic RealAlgebraic (Real.sqrt (x : ℝ)) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C x, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial RealAlgebraic ↦ p.coeff 2) h
    norm_num at hc
  · simp [Polynomial.aeval_def, Real.sq_sqrt (show 0 ≤ (x : ℝ) from hx)]

private theorem realAlgebraic_sqrt_mem (x : RealAlgebraic) (hx : 0 ≤ x) :
    Real.sqrt (x : ℝ) ∈ algebraicClosure ℚ ℝ := by
  rw [mem_algebraicClosure_iff]
  exact (realAlgebraic_sqrt_isAlgebraic x hx).restrictScalars ℚ

private theorem realAlgebraic_isSquare_of_nonneg {x : RealAlgebraic}
    (hx : 0 ≤ x) : IsSquare x := by
  let r : RealAlgebraic := ⟨Real.sqrt (x : ℝ), realAlgebraic_sqrt_mem x hx⟩
  refine ⟨r, Subtype.ext ?_⟩
  exact (Real.mul_self_sqrt (show 0 ≤ (x : ℝ) from hx)).symm

private theorem realAlgebraic_odd_polynomial_has_root {f : Polynomial RealAlgebraic}
    (hf : Odd f.natDegree) : ∃ x, f.IsRoot x := by
  let ι : RealAlgebraic →+* ℝ := algebraMap RealAlgebraic ℝ
  have hι : Function.Injective ι := FaithfulSMul.algebraMap_injective _ _
  have hdegree : (f.map ι).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hι f
  obtain ⟨r, hr⟩ := odd_degree_real_polynomial_has_root (hdegree ▸ hf)
  have hf0 : f ≠ 0 := by
    intro hfzero
    subst f
    simp at hf
  have hrAlgF : IsAlgebraic RealAlgebraic r := by
    refine ⟨f, hf0, ?_⟩
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def] using hr
  have hrAlgQ : IsAlgebraic ℚ r := hrAlgF.restrictScalars ℚ
  let x : RealAlgebraic := ⟨r, mem_algebraicClosure_iff.mpr hrAlgQ⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change ι (f.eval x) = ι 0
  rw [← Polynomial.eval₂_hom]
  change f.eval₂ ι r = 0
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hr

/-- The real algebraic numbers form a countable real-closed subfield of `ℝ`. -/
theorem realAlgebraic_isRealClosed : IsRealClosed RealAlgebraic :=
  IsRealClosed.of_linearOrderedField
    (fun {_} hx ↦ realAlgebraic_isSquare_of_nonneg hx)
    (fun {_} hf ↦ realAlgebraic_odd_polynomial_has_root hf)

/-! ### Finite transcendence supports

Choose a transcendence basis of `ℝ` over the real algebraic numbers.  Finitarity of the algebraic
matroid gives a finite subset over which each real number, hence every finite-dimensional point,
is algebraic.  This is the support existence part of Schmerl's construction; later the support is
refined to its unique minimal version and paired with a determining analytic branch.
-/

private noncomputable def realTranscendenceBasisSet : Set ℝ :=
  (exists_isTranscendenceBasis RealAlgebraic ℝ).choose

private abbrev RealTranscendenceBasisIndex : Type := realTranscendenceBasisSet

private def realTranscendenceBasisValue : RealTranscendenceBasisIndex → ℝ :=
  Subtype.val

private theorem realTranscendenceBasis_isBasis :
    IsTranscendenceBasis RealAlgebraic realTranscendenceBasisValue :=
  (exists_isTranscendenceBasis RealAlgebraic ℝ).choose_spec

private noncomputable abbrev PivotBaseField
    (t : RealTranscendenceBasisIndex) : Type :=
  IntermediateField.adjoin RealAlgebraic
    (realTranscendenceBasisValue '' ({t}ᶜ : Set RealTranscendenceBasisIndex))

private theorem pivot_transcendental
    (t : RealTranscendenceBasisIndex) :
    Transcendental (PivotBaseField t) (realTranscendenceBasisValue t) := by
  apply IntermediateField.transcendental_adjoin_iff.mpr
  exact realTranscendenceBasis_isBasis.1.transcendental_adjoin (by simp)

private theorem basisValue_mem_pivotBaseField
    {t s : RealTranscendenceBasisIndex} (hst : s ≠ t) :
    realTranscendenceBasisValue s ∈
      (IntermediateField.adjoin RealAlgebraic
        (realTranscendenceBasisValue ''
          ({t}ᶜ : Set RealTranscendenceBasisIndex))) := by
  apply IntermediateField.subset_adjoin
  exact ⟨s, by simpa [hst], rfl⟩

private noncomputable def basisValueInPivotBaseField
    (t s : RealTranscendenceBasisIndex) (hst : s ≠ t) : PivotBaseField t :=
  ⟨realTranscendenceBasisValue s, basisValue_mem_pivotBaseField hst⟩

private lemma algebraMap_basisValueInPivotBaseField
    (t s : RealTranscendenceBasisIndex) (hst : s ≠ t) :
    algebraMap (PivotBaseField t) ℝ (basisValueInPivotBaseField t s hst) =
      realTranscendenceBasisValue s := rfl

private theorem exists_finite_real_support (x : ℝ) :
    ∃ S : Set ℝ, S ⊆ realTranscendenceBasisSet ∧ S.Finite ∧
      IsAlgebraic (Algebra.adjoin RealAlgebraic S) x := by
  let M := AlgebraicIndependent.matroid RealAlgebraic ℝ
  have hbase : M.IsBase realTranscendenceBasisSet :=
    realTranscendenceBasis_isBasis
  have hx : x ∈ M.closure realTranscendenceBasisSet := by
    rw [hbase.closure_eq, AlgebraicIndependent.matroid_e]
    trivial
  obtain ⟨S, hSB, hSfin, _, hxS⟩ :=
    M.exists_mem_finite_closure_of_mem_closure hx
  refine ⟨S, hSB, hSfin, ?_⟩
  rw [AlgebraicIndependent.matroid_closure_eq] at hxS
  exact (Subalgebra.mem_algebraicClosure _ _).mp hxS

private theorem exists_finset_real_support (x : ℝ) :
    ∃ s : Finset RealTranscendenceBasisIndex,
      IsAlgebraic
        (Algebra.adjoin RealAlgebraic
          (realTranscendenceBasisValue '' (s : Set RealTranscendenceBasisIndex))) x := by
  obtain ⟨S, hSB, hSfin, hx⟩ := exists_finite_real_support x
  let S' : Set RealTranscendenceBasisIndex := realTranscendenceBasisValue ⁻¹' S
  have hS'fin : S'.Finite := hSfin.preimage Subtype.val_injective.injOn
  let s : Finset RealTranscendenceBasisIndex := hS'fin.toFinset
  have himage : realTranscendenceBasisValue '' (s : Set RealTranscendenceBasisIndex) = S := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact (hS'fin.mem_toFinset.mp ht : t ∈ S')
    · intro hz
      have hzB : z ∈ realTranscendenceBasisSet := hSB hz
      refine ⟨⟨z, hzB⟩, ?_, rfl⟩
      exact hS'fin.mem_toFinset.mpr hz
  exact ⟨s, himage ▸ hx⟩

/-- The algebraic matroid associated to `ℝ / RealAlgebraic`. -/
private noncomputable abbrev realTranscendenceMatroid :=
  AlgebraicIndependent.matroid RealAlgebraic ℝ

private theorem realTranscendenceBasis_isBase :
    realTranscendenceMatroid.IsBase realTranscendenceBasisSet :=
  realTranscendenceBasis_isBasis

/-- The unique minimal transcendence-support set of a scalar.  For a basis element it is the
singleton; otherwise it is the fundamental circuit with the scalar itself removed. -/
private noncomputable def canonicalScalarSupportSet (x : ℝ) : Set ℝ := by
  classical
  exact if x ∈ realTranscendenceBasisSet then {x}
    else realTranscendenceMatroid.fundCircuit x realTranscendenceBasisSet \ {x}

private theorem canonicalScalarSupportSet_subset (x : ℝ) :
    canonicalScalarSupportSet x ⊆ realTranscendenceBasisSet := by
  intro y hy
  by_cases hx : x ∈ realTranscendenceBasisSet
  · have hyx : y = x := by simpa [canonicalScalarSupportSet, hx] using hy
    exact hyx.symm ▸ hx
  · have hyS : y ∈ realTranscendenceMatroid.fundCircuit x
        realTranscendenceBasisSet \ {x} := by
      simpa [canonicalScalarSupportSet, hx] using hy
    have hsub := realTranscendenceMatroid.fundCircuit_subset_insert x
      realTranscendenceBasisSet hyS.1
    rcases hsub with hyx | hyB
    · exact (hyS.2 (by simpa [hyx])).elim
    · exact hyB

private theorem canonicalScalarSupportSet_finite (x : ℝ) :
    (canonicalScalarSupportSet x).Finite := by
  by_cases hx : x ∈ realTranscendenceBasisSet
  · simp [canonicalScalarSupportSet, hx]
  · have hc : realTranscendenceMatroid.IsCircuit
        (realTranscendenceMatroid.fundCircuit x realTranscendenceBasisSet) :=
      realTranscendenceBasis_isBase.fundCircuit_isCircuit
        (by simp [realTranscendenceMatroid, AlgebraicIndependent.matroid_e]) hx
    have hfin : (realTranscendenceMatroid.fundCircuit x
        realTranscendenceBasisSet \ {x}).Finite := hc.finite.sdiff
    simpa [canonicalScalarSupportSet, hx] using hfin

private noncomputable def scalarTranscendenceSupport (x : ℝ) :
    Finset RealTranscendenceBasisIndex := by
  let S : Set RealTranscendenceBasisIndex :=
    realTranscendenceBasisValue ⁻¹' canonicalScalarSupportSet x
  have hSfin : S.Finite := (canonicalScalarSupportSet_finite x).preimage
    Subtype.val_injective.injOn
  exact hSfin.toFinset

private theorem mem_scalarTranscendenceSupport_iff (x : ℝ)
    (z : RealTranscendenceBasisIndex) :
    z ∈ scalarTranscendenceSupport x ↔ z.1 ∈ canonicalScalarSupportSet x := by
  classical
  simp [scalarTranscendenceSupport, realTranscendenceBasisValue]

private theorem scalarTranscendenceSupport_image (x : ℝ) :
    realTranscendenceBasisValue ''
      (scalarTranscendenceSupport x : Set RealTranscendenceBasisIndex) =
        canonicalScalarSupportSet x := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_scalarTranscendenceSupport_iff x z).mp hz
  · intro hy
    refine ⟨⟨y, canonicalScalarSupportSet_subset x hy⟩, ?_, rfl⟩
    exact (mem_scalarTranscendenceSupport_iff x _).mpr hy

private theorem mem_closure_canonicalScalarSupportSet (x : ℝ) :
    x ∈ realTranscendenceMatroid.closure (canonicalScalarSupportSet x) := by
  by_cases hx : x ∈ realTranscendenceBasisSet
  · apply realTranscendenceMatroid.subset_closure
      (X := canonicalScalarSupportSet x)
      (by simp [realTranscendenceMatroid, AlgebraicIndependent.matroid_e])
    simp [canonicalScalarSupportSet, hx]
  · have hc : realTranscendenceMatroid.IsCircuit
        (realTranscendenceMatroid.fundCircuit x realTranscendenceBasisSet) :=
      realTranscendenceBasis_isBase.fundCircuit_isCircuit
        (by simp [realTranscendenceMatroid, AlgebraicIndependent.matroid_e]) hx
    have hmem := hc.mem_closure_sdiff_singleton_of_mem
      (realTranscendenceMatroid.mem_fundCircuit x realTranscendenceBasisSet)
    simpa [canonicalScalarSupportSet, hx] using hmem

private theorem scalarTranscendenceSupport_spec (x : ℝ) :
    IsAlgebraic
      (Algebra.adjoin RealAlgebraic
        (realTranscendenceBasisValue ''
          (scalarTranscendenceSupport x : Set RealTranscendenceBasisIndex))) x :=
  by
    rw [scalarTranscendenceSupport_image]
    have hx := mem_closure_canonicalScalarSupportSet x
    rw [AlgebraicIndependent.matroid_closure_eq] at hx
    exact (Subalgebra.mem_algebraicClosure _ _).mp hx

private theorem canonicalScalarSupportSet_minimal (x : ℝ) {S : Set ℝ}
    (hSB : S ⊆ realTranscendenceBasisSet)
    (hxS : IsAlgebraic (Algebra.adjoin RealAlgebraic S) x) :
    canonicalScalarSupportSet x ⊆ S := by
  have hxcl : x ∈ realTranscendenceMatroid.closure S := by
    rw [AlgebraicIndependent.matroid_closure_eq]
    exact (Subalgebra.mem_algebraicClosure _ _).mpr hxS
  by_cases hx : x ∈ realTranscendenceBasisSet
  · have hxmem : x ∈ S := by
      by_contra hxS'
      have hSind : realTranscendenceMatroid.Indep S :=
        realTranscendenceBasis_isBase.indep.subset hSB
      have hdep : realTranscendenceMatroid.Dep (Set.insert x S) :=
        (hSind.mem_closure_iff_of_notMem hxS').mp hxcl
      exact hdep.not_indep
        (realTranscendenceBasis_isBase.indep.subset (Set.insert_subset hx hSB))
    simpa [canonicalScalarSupportSet, hx] using hxmem
  · rw [canonicalScalarSupportSet, if_neg hx]
    intro y hy
    have hyinter : y ∈ ⋂₀ {J : Set ℝ |
        J ⊆ realTranscendenceBasisSet ∧
          x ∈ realTranscendenceMatroid.closure J} := by
      have heq := realTranscendenceMatroid.fundCircuit_eq_sInter
        (e := x) (I := realTranscendenceBasisSet)
        (by rw [realTranscendenceBasis_isBase.closure_eq]
            simp [realTranscendenceMatroid, AlgebraicIndependent.matroid_e])
      rw [heq] at hy
      rcases hy.1 with hyx | hyi
      · exact (hy.2 (by simp [hyx])).elim
      · exact hyi
    exact hyinter S ⟨hSB, hxcl⟩

private noncomputable def pointTranscendenceSupport {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : Finset RealTranscendenceBasisIndex :=
  Finset.univ.biUnion fun i ↦ scalarTranscendenceSupport (x i)

private theorem scalarSupport_subset_pointSupport {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    scalarTranscendenceSupport (x i) ⊆ pointTranscendenceSupport x := by
  exact Finset.subset_biUnion_of_mem
    (fun j ↦ scalarTranscendenceSupport (x j)) (Finset.mem_univ i)

private theorem pointTranscendenceSupport_spec {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    IsAlgebraic
      (Algebra.adjoin RealAlgebraic
        (realTranscendenceBasisValue ''
          (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex))) (x i) := by
  let A := Algebra.adjoin RealAlgebraic
    (realTranscendenceBasisValue ''
      (scalarTranscendenceSupport (x i) : Set RealTranscendenceBasisIndex))
  let A' := Algebra.adjoin RealAlgebraic
    (realTranscendenceBasisValue ''
      (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex))
  have hset :
      (scalarTranscendenceSupport (x i) : Set RealTranscendenceBasisIndex) ⊆
        (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex) := by
    intro z hz
    exact scalarSupport_subset_pointSupport x i hz
  have hle : A ≤ A' := Algebra.adjoin_mono (Set.image_mono hset)
  exact (scalarTranscendenceSupport_spec (x i)).tower_top_of_subalgebra_le hle

private theorem pointTranscendenceSupport_minimal {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) {S : Set ℝ}
    (hSB : S ⊆ realTranscendenceBasisSet)
    (hxS : ∀ i : Fin n, IsAlgebraic (Algebra.adjoin RealAlgebraic S) (x i)) :
    realTranscendenceBasisValue ''
      (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex) ⊆ S := by
  rintro _ ⟨t, ht, rfl⟩
  change t ∈ pointTranscendenceSupport x at ht
  rw [pointTranscendenceSupport, Finset.mem_biUnion] at ht
  obtain ⟨i, _, hti⟩ := ht
  exact canonicalScalarSupportSet_minimal (x i) hSB (hxS i)
    ((mem_scalarTranscendenceSupport_iff (x i) t).mp hti)

/-- The increasing real tuple enumerating the canonical finite support of a point. -/
private noncomputable def pointSupportTuple {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Fin (pointTranscendenceSupport x).card → ℝ :=
  fun j ↦ realTranscendenceBasisValue
    ((pointTranscendenceSupport x).orderEmbOfFin rfl j)

private theorem range_pointSupportTuple {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Set.range (pointSupportTuple x) =
      realTranscendenceBasisValue ''
        (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex) := by
  change Set.range (realTranscendenceBasisValue ∘
      (pointTranscendenceSupport x).orderEmbOfFin rfl) = _
  rw [Set.range_comp,
    Finset.range_orderEmbOfFin (pointTranscendenceSupport x) rfl]

private theorem pointSupportTuple_algebraicIndependent {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    AlgebraicIndependent RealAlgebraic (pointSupportTuple x) := by
  have h := realTranscendenceBasis_isBasis.1.comp
    ((pointTranscendenceSupport x).orderEmbOfFin rfl)
    ((pointTranscendenceSupport x).orderEmbOfFin rfl).injective
  change AlgebraicIndependent RealAlgebraic
    (realTranscendenceBasisValue ∘
      (pointTranscendenceSupport x).orderEmbOfFin rfl)
  exact h

private theorem pointSupportTuple_coordinate_isAlgebraic {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    IsAlgebraic
      (IntermediateField.adjoin RealAlgebraic
        (Set.range (pointSupportTuple x))) (x i) := by
  have h := pointTranscendenceSupport_spec x i
  rw [← range_pointSupportTuple] at h
  exact h.tower_top_of_subalgebra_le
    (IntermediateField.algebra_adjoin_le_adjoin RealAlgebraic
      (Set.range (pointSupportTuple x)))

private theorem isAlgebraic_realAlgebraic_of_scalarSupport_empty {x : ℝ}
    (hx : scalarTranscendenceSupport x = ∅) : IsAlgebraic RealAlgebraic x := by
  have hs := scalarTranscendenceSupport_spec x
  rw [hx] at hs
  have himage : realTranscendenceBasisValue ''
      ((∅ : Finset RealTranscendenceBasisIndex) : Set RealTranscendenceBasisIndex) =
        (∅ : Set ℝ) := by simp
  rw [himage, Algebra.adjoin_empty] at hs
  exact Subalgebra.isAlgebraic_of_isAlgebraic_bot hs

private theorem scalarSupport_empty_of_pointSupport_empty {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (hx : pointTranscendenceSupport x = ∅) (i : Fin n) :
    scalarTranscendenceSupport (x i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hmem := scalarSupport_subset_pointSupport x i ht
  rw [hx] at hmem
  simpa using hmem

private theorem isAlgebraic_rat_of_pointSupport_empty {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (hx : pointTranscendenceSupport x = ∅) (i : Fin n) :
    IsAlgebraic ℚ (x i) :=
  (isAlgebraic_realAlgebraic_of_scalarSupport_empty
    (scalarSupport_empty_of_pointSupport_empty x hx i)).restrictScalars ℚ

private def EmptySupportPoint (n : ℕ) :=
  {x : EuclideanSpace ℝ (Fin n) // pointTranscendenceSupport x = ∅}

private noncomputable def emptySupportPointToAlgebraicCoordinates {n : ℕ} :
    EmptySupportPoint n → (Fin n → RealAlgebraic) :=
  fun x i ↦ ⟨x.1 i, mem_algebraicClosure_iff.mpr
    (isAlgebraic_rat_of_pointSupport_empty x.1 x.2 i)⟩

private theorem emptySupportPointToAlgebraicCoordinates_injective {n : ℕ} :
    Function.Injective (emptySupportPointToAlgebraicCoordinates (n := n)) := by
  intro x y hxy
  apply Subtype.ext
  ext i
  exact congrArg Subtype.val (congrFun hxy i)

private theorem emptySupportPoint_countable (n : ℕ) : Countable (EmptySupportPoint n) :=
  emptySupportPointToAlgebraicCoordinates_injective.countable

private noncomputable def emptySupportPointCode (n : ℕ) : EmptySupportPoint n ↪ ℕ := by
  letI : Countable (EmptySupportPoint n) := emptySupportPoint_countable n
  letI : Encodable (EmptySupportPoint n) := Encodable.ofCountable _
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

/-! ### Countable algebraic chart codes

A chart code consists of one polynomial equation for each output coordinate and rational open
boxes for the input and output.  On a box where every equation has a unique output root, the code
determines an actual function without storing any real parameter.  This is important: there are
only countably many codes, and two points carrying the same code literally use the same branch.
-/

private noncomputable instance countableAddMonoidAlgebra
    {R M : Type*} [Semiring R] [Countable R] [Countable M] :
    Countable (AddMonoidAlgebra R M) :=
  AddMonoidAlgebra.coeff_injective.countable

private noncomputable instance countableRealAlgebraicMvPolynomial (k : ℕ) :
    Countable (MvPolynomial (Fin k) RealAlgebraic) :=
  AddMonoidAlgebra.coeff_injective.countable

private noncomputable instance countableRealAlgebraicPolynomialMvPolynomial (k : ℕ) :
    Countable (Polynomial (MvPolynomial (Fin k) RealAlgebraic)) :=
  Polynomial.toFinsupp_injective.countable

private abbrev AlgebraicChartCode (n : ℕ) :=
  Σ k : ℕ,
    (Fin n → Polynomial (MvPolynomial (Fin k) RealAlgebraic)) ×
      (Fin k → ℚ × ℚ) × (Fin n → ℚ × ℚ)

private noncomputable instance (n : ℕ) : Countable (AlgebraicChartCode n) := by
  dsimp only [AlgebraicChartCode]
  infer_instance

private noncomputable def algebraicChartCodeEmbedding (n : ℕ) :
    AlgebraicChartCode n ↪ ℕ := by
  letI : Encodable (AlgebraicChartCode n) := Encodable.ofCountable _
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

private noncomputable def evalChartPolynomial {k : ℕ}
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic))
    (u : Fin k → ℝ) (y : ℝ) : ℝ :=
  P.eval₂ (MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) u) y

private noncomputable def specializeMvPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K) (j : Fin k) :
    MvPolynomial (Fin k) RealAlgebraic →+* Polynomial K :=
  MvPolynomial.eval₂Hom
    ((algebraMap K (Polynomial K)).comp (algebraMap RealAlgebraic K))
    (fun l ↦ if l = j then Polynomial.X else Polynomial.C (fixed l))

private noncomputable def specializeChartPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K) (j : Fin k)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) :
    Polynomial (Polynomial K) :=
  P.map (specializeMvPolynomial fixed j)

private lemma eval_specializeMvPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {k : ℕ} (fixed : Fin k → K) (j : Fin k)
    (q : MvPolynomial (Fin k) RealAlgebraic) (z : ℝ) :
    (specializeMvPolynomial fixed j q).eval₂ (algebraMap K ℝ) z =
      MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ)
        (Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z) q := by
  let f : MvPolynomial (Fin k) RealAlgebraic →+* ℝ :=
    (Polynomial.eval₂RingHom (algebraMap K ℝ) z).comp
      (specializeMvPolynomial fixed j)
  let g : MvPolynomial (Fin k) RealAlgebraic →+* ℝ :=
    MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ)
      (Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z)
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, g, specializeMvPolynomial,
        IsScalarTower.algebraMap_apply RealAlgebraic K ℝ]
    · intro l
      by_cases hlj : l = j
      · subst l
        simp [f, g, specializeMvPolynomial, Function.update]
      · simp [f, g, specializeMvPolynomial, Function.update, hlj]
  exact RingHom.congr_fun hfg q

private lemma eval_specializeChartPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {k : ℕ} (fixed : Fin k → K) (j : Fin k)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) (z y : ℝ) :
    evalBivariateOver (specializeChartPolynomial fixed j P) z y =
      evalChartPolynomial P
        (Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z) y := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [specializeChartPolynomial, evalBivariateOver,
        evalChartPolynomial] at hp hq ⊢
      rw [Polynomial.map_add, Polynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial m q =>
      calc
        evalBivariateOver
              (specializeChartPolynomial fixed j (Polynomial.monomial m q)) z y =
            (specializeMvPolynomial fixed j q).eval₂ (algebraMap K ℝ) z * y ^ m := by
              simp [specializeChartPolynomial, evalBivariateOver]
        _ = MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ)
              (Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z) q * y ^ m := by
              rw [eval_specializeMvPolynomial]
        _ = evalChartPolynomial (Polynomial.monomial m q)
              (Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z) y := by
              simp [evalChartPolynomial]

private lemma specializeChartPolynomial_derivative
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K) (j : Fin k)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) :
    specializeChartPolynomial fixed j P.derivative =
      (specializeChartPolynomial fixed j P).derivative := by
  simp [specializeChartPolynomial, Polynomial.derivative_map]

private noncomputable def specializeAllMvPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K) :
    MvPolynomial (Fin k) RealAlgebraic →+* K :=
  MvPolynomial.eval₂Hom (algebraMap RealAlgebraic K) fixed

private noncomputable def specializeAllChartPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) : Polynomial K :=
  P.map (specializeAllMvPolynomial fixed)

private lemma eval_specializeAllMvPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {k : ℕ} (fixed : Fin k → K)
    (q : MvPolynomial (Fin k) RealAlgebraic) :
    algebraMap K ℝ (specializeAllMvPolynomial fixed q) =
      MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ)
        (fun l ↦ algebraMap K ℝ (fixed l)) q := by
  let f : MvPolynomial (Fin k) RealAlgebraic →+* ℝ :=
    (algebraMap K ℝ).comp (specializeAllMvPolynomial fixed)
  let g : MvPolynomial (Fin k) RealAlgebraic →+* ℝ :=
    MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ)
      (fun l ↦ algebraMap K ℝ (fixed l))
  have hfg : f = g := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, g, specializeAllMvPolynomial,
        IsScalarTower.algebraMap_apply RealAlgebraic K ℝ]
    · intro l
      simp [f, g, specializeAllMvPolynomial]
  exact RingHom.congr_fun hfg q

private lemma eval_specializeAllChartPolynomial
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {k : ℕ} (fixed : Fin k → K)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) (y : ℝ) :
    (specializeAllChartPolynomial fixed P).eval₂ (algebraMap K ℝ) y =
      evalChartPolynomial P (fun l ↦ algebraMap K ℝ (fixed l)) y := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [specializeAllChartPolynomial, evalChartPolynomial] at hp hq ⊢
      rw [Polynomial.map_add, Polynomial.eval₂_add, Polynomial.eval₂_add, hp, hq]
  | monomial m q =>
      simp [specializeAllChartPolynomial, evalChartPolynomial,
        eval_specializeAllMvPolynomial]

private lemma specializeAllChartPolynomial_derivative
    {K : Type*} [Field K] [Algebra RealAlgebraic K]
    {k : ℕ} (fixed : Fin k → K)
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic)) :
    specializeAllChartPolynomial fixed P.derivative =
      (specializeAllChartPolynomial fixed P).derivative := by
  simp [specializeAllChartPolynomial, Polynomial.derivative_map]

/-! A coordinate algebraic over the rational-function field generated by an algebraically
independent tuple satisfies an equation with polynomial (rather than rational-function)
coefficients whose vertical derivative is nonzero.  This is the separable equation to which the
analytic implicit-function theorem is applied below. -/

private theorem exists_separable_chart_polynomial {k : ℕ}
    (u : Fin k → ℝ) (hu : AlgebraicIndependent RealAlgebraic u) (x : ℝ)
    (hx : IsAlgebraic
      (IntermediateField.adjoin RealAlgebraic (Set.range u)) x) :
    ∃ P : Polynomial (MvPolynomial (Fin k) RealAlgebraic),
      evalChartPolynomial P u x = 0 ∧
        evalChartPolynomial P.derivative u x ≠ 0 := by
  classical
  let R := MvPolynomial (Fin k) RealAlgebraic
  let K := FractionRing R
  let L := IntermediateField.adjoin RealAlgebraic (Set.range u)
  let e : K ≃ₐ[RealAlgebraic] L := hu.aevalEquivField
  let r : L →ₐ[RealAlgebraic] K := hu.reprField
  let ev : K →+* ℝ :=
    IsFractionRing.lift (algebraicIndependent_iff_injective_aeval.mpr hu)
  let m : Polynomial L := minpoly L x
  let q : Polynomial K := m.map r
  let P : Polynomial R :=
    IsLocalization.integerNormalization (nonZeroDivisors R) q
  have hmroot : Polynomial.aeval x m = 0 := minpoly.aeval L x
  have hmsep : m.Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hx.isIntegral)
  have hmderiv : Polynomial.aeval x m.derivative ≠ 0 :=
    hmsep.aeval_derivative_ne_zero hmroot
  have hev_r : ev.comp r.toRingHom = IntermediateField.val L := by
    ext z
    exact hu.lift_reprField z
  have hqroot : q.eval₂ ev x = 0 := by
    rw [show q = m.map r by rfl, Polynomial.eval₂_map]
    change Polynomial.eval₂ (ev.comp r.toRingHom) x m = 0
    rw [hev_r]
    have hval : algebraMap L ℝ = IntermediateField.val L := rfl
    change Polynomial.eval₂ (algebraMap L ℝ) x m = 0 at hmroot
    rw [hval] at hmroot
    exact hmroot
  have hqderiv : q.derivative.eval₂ ev x ≠ 0 := by
    rw [show q = m.map r by rfl, Polynomial.derivative_map,
      Polynomial.eval₂_map]
    change Polynomial.eval₂ (ev.comp r.toRingHom) x m.derivative ≠ 0
    rw [hev_r]
    have hval : algebraMap L ℝ = IntermediateField.val L := rfl
    change Polynomial.eval₂ (algebraMap L ℝ) x m.derivative ≠ 0 at hmderiv
    rw [hval] at hmderiv
    exact hmderiv
  obtain ⟨b, hb, hPmap⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors R) q
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hevb0 : ev (algebraMap R K b) ≠ 0 := by
    exact (map_ne_zero ev).mpr
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
  have hev_alg : ev.comp (algebraMap R K) =
      MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) u := by
    apply MvPolynomial.ringHom_ext
    · intro a
      calc
        ev (algebraMap R K (MvPolynomial.C a)) =
            MvPolynomial.aeval u (MvPolynomial.C a) :=
          IsFractionRing.lift_algebraMap
            (algebraicIndependent_iff_injective_aeval.mpr hu) _
        _ = (a : ℝ) := by simp
        _ = MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) u
            (MvPolynomial.C a) := by simp
    · intro j
      calc
        ev (algebraMap R K (MvPolynomial.X j)) =
            MvPolynomial.aeval u (MvPolynomial.X j) :=
          IsFractionRing.lift_algebraMap
            (algebraicIndependent_iff_injective_aeval.mpr hu) _
        _ = u j := by simp
        _ = MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) u
            (MvPolynomial.X j) := by simp
  refine ⟨P, ?_, ?_⟩
  · have hzero : (P.map (algebraMap R K)).eval₂ ev x = 0 := by
      rw [hPmap]
      rw [← IsScalarTower.algebraMap_smul K b q,
        Polynomial.eval₂_smul, hqroot, mul_zero]
    rw [Polynomial.eval₂_map] at hzero
    rw [hev_alg] at hzero
    simpa only [P, R, evalChartPolynomial] using hzero
  · intro hzero
    have hzero' : ((P.derivative).map (algebraMap R K)).eval₂ ev x = 0 := by
      rw [Polynomial.eval₂_map]
      rw [hev_alg]
      simpa only [P, R, evalChartPolynomial] using hzero
    have hdmap := congrArg Polynomial.derivative
      (hPmap.trans (IsScalarTower.algebraMap_smul K b q).symm)
    rw [Polynomial.derivative_map, Polynomial.derivative_smul] at hdmap
    rw [hdmap, Polynomial.eval₂_smul] at hzero'
    exact (mul_ne_zero hevb0 hqderiv) hzero'

private theorem exists_point_chart_polynomials {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ P : Fin n →
        Polynomial (MvPolynomial (Fin (pointTranscendenceSupport x).card) RealAlgebraic),
      ∀ i : Fin n,
        evalChartPolynomial (P i) (pointSupportTuple x) (x i) = 0 ∧
          evalChartPolynomial (P i).derivative (pointSupportTuple x) (x i) ≠ 0 := by
  choose P hP using fun i : Fin n ↦
    exists_separable_chart_polynomial (pointSupportTuple x)
      (pointSupportTuple_algebraicIndependent x) (x i)
      (pointSupportTuple_coordinate_isAlgebraic x i)
  exact ⟨P, hP⟩

private lemma analyticAt_evalChartCoefficient {k : ℕ}
    (q : MvPolynomial (Fin k) RealAlgebraic) (z : (Fin k → ℝ) × ℝ) :
    AnalyticAt ℝ
      (fun w : (Fin k → ℝ) × ℝ ↦
        MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) w.1 q) z := by
  have hcoord : ∀ j : Fin k,
      AnalyticAt ℝ (fun w : (Fin k → ℝ) × ℝ ↦ w.1 j) z := by
    intro j
    have hproj := (ContinuousLinearMap.proj (R := ℝ) j).analyticAt z.1
    have hcomp := hproj.comp analyticAt_fst
    change AnalyticAt ℝ (fun w : (Fin k → ℝ) × ℝ ↦ w.1 j) z at hcomp
    exact hcomp
  induction q using MvPolynomial.induction_on with
  | C a =>
      simpa using (analyticAt_const :
        AnalyticAt ℝ (fun _ : (Fin k → ℝ) × ℝ ↦ (a : ℝ)) z)
  | add p q hp hq =>
      have hadd : AnalyticAt ℝ
          (fun w : (Fin k → ℝ) × ℝ ↦
            MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) w.1 p +
              MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) w.1 q) z :=
        hp.add hq
      simpa only [map_add] using hadd
  | mul_X p j hp =>
      have hmul : AnalyticAt ℝ
          (fun w : (Fin k → ℝ) × ℝ ↦
            MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) w.1 p * w.1 j) z :=
        hp.mul (hcoord j)
      simpa only [map_mul, MvPolynomial.eval₂Hom_X'] using hmul

private lemma analyticAt_evalChartPolynomial {k : ℕ}
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic))
    (z : (Fin k → ℝ) × ℝ) :
    AnalyticAt ℝ
      (fun w : (Fin k → ℝ) × ℝ ↦ evalChartPolynomial P w.1 w.2) z := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [show (fun w : (Fin k → ℝ) × ℝ ↦
          evalChartPolynomial (p + q) w.1 w.2) =
          (fun w ↦ evalChartPolynomial p w.1 w.2 +
            evalChartPolynomial q w.1 w.2) by
        funext w
        simp [evalChartPolynomial]]
      exact hp.add hq
  | monomial m q =>
      rw [show (fun w : (Fin k → ℝ) × ℝ ↦
          evalChartPolynomial (Polynomial.monomial m q) w.1 w.2) =
          (fun w ↦
            MvPolynomial.eval₂Hom (algebraMap RealAlgebraic ℝ) w.1 q * w.2 ^ m) by
        funext w
        simp [evalChartPolynomial]]
      exact (analyticAt_evalChartCoefficient q z).mul (analyticAt_snd.pow m)

private lemma fderiv_evalChartPolynomial_vertical {k : ℕ}
    (P : Polynomial (MvPolynomial (Fin k) RealAlgebraic))
    (u : Fin k → ℝ) (y : ℝ) :
    fderiv ℝ (fun z : (Fin k → ℝ) × ℝ ↦
        evalChartPolynomial P z.1 z.2) (u, y) (0, 1) =
      evalChartPolynomial P.derivative u y := by
  let f : (Fin k → ℝ) × ℝ → ℝ := fun z ↦
    evalChartPolynomial P z.1 z.2
  let e : ℝ → (Fin k → ℝ) × ℝ := fun z ↦ (u, z)
  have hf : DifferentiableAt ℝ f (e y) :=
    (analyticAt_evalChartPolynomial P (u, y)).differentiableAt
  have hconst : DifferentiableAt ℝ (fun _ : ℝ ↦ u) y :=
    differentiableAt_const u
  have he : DifferentiableAt ℝ e y := hconst.prodMk differentiableAt_id
  have heval : fderiv ℝ e y 1 = (0, 1) := by
    rw [show fderiv ℝ e y =
        (fderiv ℝ (fun _ : ℝ ↦ u) y).prod (fderiv ℝ (fun z : ℝ ↦ z) y) by
      exact hconst.fderiv_prodMk differentiableAt_id]
    simp
  have hcomp := fderiv_comp (x := y) (g := f) (f := e) hf he
  have happ := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) hcomp
  rw [ContinuousLinearMap.comp_apply, heval] at happ
  have hpoly : f ∘ e = fun z ↦
      ((P.map (MvPolynomial.eval₂Hom
        (algebraMap RealAlgebraic ℝ) u)).eval z) := by
    funext z
    simp [f, e, evalChartPolynomial, Polynomial.eval₂_eq_eval_map]
  rw [hpoly, Polynomial.fderiv] at happ
  simpa [f, e, evalChartPolynomial, Polynomial.derivative_map,
    Polynomial.eval₂_eq_eval_map] using happ.symm

private def inRationalInterval (ab : ℚ × ℚ) (x : ℝ) : Prop :=
  (ab.1 : ℝ) < x ∧ x < (ab.2 : ℝ)

private def chartInputBox {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) : Prop :=
  ∀ j, inRationalInterval (c.2.2.1 j) (u j)

private def chartRoot {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) (i : Fin n) (y : ℝ) : Prop :=
  inRationalInterval (c.2.2.2 i) y ∧
    evalChartPolynomial (c.2.1 i) u y = 0

private noncomputable def chartValue {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) (i : Fin n) : ℝ := by
  classical
  exact if h : ∃! y, chartRoot c u i y then h.exists.choose else 0

private noncomputable def chartPoint {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ chartValue c u i)

private lemma chartValue_root {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) (i : Fin n) (h : ∃! y, chartRoot c u i y) :
    chartRoot c u i (chartValue c u i) := by
  simp only [chartValue, dif_pos h]
  exact h.exists.choose_spec

private lemma chartValue_eq_of_root {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) (i : Fin n) (h : ∃! y, chartRoot c u i y)
    {y : ℝ} (hy : chartRoot c u i y) : chartValue c u i = y := by
  exact h.unique (chartValue_root c u i h) hy

/-! The analytic implicit branch used by a chart.  We first record a general local inverse for an
analytic map with invertible derivative, and then the elementary triangular linear equivalence
which applies to `(x,y) ↦ (x,p(x,y))` when the `y` derivative of `p` is nonzero. -/

private lemma strictFDerivOfAnalyticEquiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : E → E} {u : E} (hH : AnalyticAt ℝ H u) (i : E ≃L[ℝ] E)
    (hi : fderiv ℝ H u = i) :
    HasStrictFDerivAt H (i : E →L[ℝ] E) u := by
  rw [← hi]
  exact hH.hasStrictFDerivAt

private noncomputable def analyticLocalInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : E → E} {u : E} (hH : AnalyticAt ℝ H u) (i : E ≃L[ℝ] E)
    (hi : fderiv ℝ H u = i) : E → E :=
  ((strictFDerivOfAnalyticEquiv hH i hi).toOpenPartialHomeomorph H).symm

private lemma analyticAt_analyticLocalInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : E → E} {u : E} (hH : AnalyticAt ℝ H u) (i : E ≃L[ℝ] E)
    (hi : fderiv ℝ H u = i) :
    AnalyticAt ℝ (analyticLocalInverse hH i hi) (H u) := by
  let hHi := strictFDerivOfAnalyticEquiv hH i hi
  let R := hHi.toOpenPartialHomeomorph H
  have hu : u ∈ R.source := hHi.mem_toOpenPartialHomeomorph_source
  change AnalyticAt ℝ R.symm (H u)
  apply R.analyticAt_symm' hu
  · simpa [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hH
  · simpa [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hi

private lemma analyticLocalInverse_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : E → E} {u : E} (hH : AnalyticAt ℝ H u) (i : E ≃L[ℝ] E)
    (hi : fderiv ℝ H u = i) :
    analyticLocalInverse hH i hi (H u) = u := by
  let hHi := strictFDerivOfAnalyticEquiv hH i hi
  let R := hHi.toOpenPartialHomeomorph H
  have hu : u ∈ R.source := hHi.mem_toOpenPartialHomeomorph_source
  change R.symm (H u) = u
  simpa [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using R.left_inv hu

private lemma eventually_apply_analyticLocalInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {H : E → E} {u : E} (hH : AnalyticAt ℝ H u) (i : E ≃L[ℝ] E)
    (hi : fderiv ℝ H u = i) :
    ∀ᶠ z in nhds (H u), H (analyticLocalInverse hH i hi z) = z := by
  let hHi := strictFDerivOfAnalyticEquiv hH i hi
  let R := hHi.toOpenPartialHomeomorph H
  have hu : u ∈ R.source := hHi.mem_toOpenPartialHomeomorph_source
  change ∀ᶠ z in nhds (H u), H (R.symm z) = z
  simpa [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using
    R.eventually_right_inverse' hu

private def triangularContinuousLinearMap
    (L : (ℝ × ℝ) →L[ℝ] ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod L

private lemma triangularContinuousLinearMap_injective
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    Function.Injective (triangularContinuousLinearMap L) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz1 : z.1 = 0 := congrArg Prod.fst hz
  have hz2 : L z = 0 := congrArg Prod.snd hz
  apply Prod.ext
  · exact hz1
  · have hdecomp : z = z.1 • (1, 0) + z.2 • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul, hz1, zero_smul, zero_add] at hz2
    exact (smul_eq_zero.mp hz2).resolve_right hL

private lemma triangularContinuousLinearMap_surjective
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    Function.Surjective (triangularContinuousLinearMap L) := by
  intro z
  let y : ℝ := (z.2 - L (z.1, 0)) / L (0, 1)
  refine ⟨(z.1, y), ?_⟩
  apply Prod.ext
  · rfl
  · change L (z.1, y) = z.2
    have hdecomp : (z.1, y) = z.1 • (1, 0) + y • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul, map_smul]
    dsimp [y]
    have hz10 : L (z.1, 0) = z.1 * L (1, 0) := by
      convert L.map_smul z.1 (1, 0) using 1 <;> simp [smul_eq_mul]
    rw [← hz10]
    field_simp [hL]
    ring

private noncomputable def triangularContinuousLinearEquiv
    (L : (ℝ × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  ContinuousLinearEquiv.ofBijective (triangularContinuousLinearMap L)
    (LinearMap.ker_eq_bot.mpr (triangularContinuousLinearMap_injective L hL))
    (LinearMap.range_eq_top.mpr (triangularContinuousLinearMap_surjective L hL))

private lemma fderiv_fst_prod
    {p : ℝ × ℝ → ℝ} {u : ℝ × ℝ} (hp : DifferentiableAt ℝ p u) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ (z.1, p z)) u =
      triangularContinuousLinearMap (fderiv ℝ p u) := by
  rw [differentiableAt_fst.fderiv_prodMk hp, fderiv_fst]
  rfl

private lemma fderiv_fst_prod_equiv
    {p : ℝ × ℝ → ℝ} {u : ℝ × ℝ} (hp : DifferentiableAt ℝ p u)
    (hpartial : fderiv ℝ p u (0, 1) ≠ 0) :
    fderiv ℝ (fun z : ℝ × ℝ ↦ (z.1, p z)) u =
      (triangularContinuousLinearEquiv (fderiv ℝ p u) hpartial :
        (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := by
  rw [fderiv_fst_prod hp]
  exact (ContinuousLinearEquiv.coe_ofBijective _ _ _).symm

private theorem exists_analytic_implicit_branch
    {p : ℝ × ℝ → ℝ} {u : ℝ × ℝ} (hp : AnalyticAt ℝ p u)
    (hpartial : fderiv ℝ p u (0, 1) ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      AnalyticAt ℝ ψ u.1 ∧ ψ u.1 = u.2 ∧
        ∀ᶠ z in nhds u.1, p (z, ψ z) = p u := by
  let H : ℝ × ℝ → ℝ × ℝ := fun z ↦ (z.1, p z)
  have hH : AnalyticAt ℝ H u := analyticAt_fst.prod hp
  let i : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    triangularContinuousLinearEquiv (fderiv ℝ p u) hpartial
  have hi : fderiv ℝ H u = (i : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) :=
    fderiv_fst_prod_equiv hp.differentiableAt hpartial
  let r : ℝ × ℝ → ℝ × ℝ := analyticLocalInverse hH i hi
  let ψ : ℝ → ℝ := fun z ↦ (r (z, p u)).2
  refine ⟨ψ, ?_, ?_, ?_⟩
  · have hpair : AnalyticAt ℝ (fun z : ℝ ↦ (z, p u)) u.1 :=
      analyticAt_id.prod analyticAt_const
    have hr : AnalyticAt ℝ r (H u) := analyticAt_analyticLocalInverse hH i hi
    have hcomp : AnalyticAt ℝ (fun z : ℝ ↦ r (z, p u)) u.1 := by
      have hc := hr.comp_of_eq hpair (by simp [H])
      change AnalyticAt ℝ (fun z : ℝ ↦ r (z, p u)) u.1 at hc
      exact hc
    have hs := analyticAt_snd.comp hcomp
    change AnalyticAt ℝ (fun z : ℝ ↦ (r (z, p u)).2) u.1 at hs
    exact hs
  · have hinv := analyticLocalInverse_apply hH i hi
    exact congrArg Prod.snd hinv
  · have hright := eventually_apply_analyticLocalInverse hH i hi
    have hpair : Filter.Tendsto (fun z : ℝ ↦ (z, p u))
        (nhds u.1) (nhds (H u)) := by
      simpa [H] using
        (analyticAt_id.prod analyticAt_const :
          AnalyticAt ℝ (fun z : ℝ ↦ (z, p u)) u.1).continuousAt.tendsto
    filter_upwards [hpair.eventually hright] with z hz
    have hz1 := congrArg Prod.fst hz
    have hz2 := congrArg Prod.snd hz
    change (r (z, p u)).1 = z at hz1
    change p (r (z, p u)) = p u at hz2
    change p (z, (r (z, p u)).2) = p u
    have hpairEq : (z, (r (z, p u)).2) = r (z, p u) :=
      Prod.ext hz1.symm rfl
    rw [hpairEq]
    exact hz2

/-! The same triangular inverse-function argument in an arbitrary finite-dimensional input
space.  Besides analyticity, we retain the open source on which `(v,y) ↦ (v,p(v,y))` is
injective; a rational product box inside that source gives the global uniqueness clause in an
`AlgebraicChartCode`. -/

private def triangularContinuousLinearMapGeneral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (E × ℝ) →L[ℝ] ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
  (ContinuousLinearMap.fst ℝ E ℝ).prod L

private lemma triangularContinuousLinearMapGeneral_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (E × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    Function.Injective (triangularContinuousLinearMapGeneral L) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hz1 : z.1 = 0 := congrArg Prod.fst hz
  have hz2 : L z = 0 := congrArg Prod.snd hz
  refine Prod.ext hz1 ?_
  have hdecomp : z = (z.1, 0) + z.2 • (0, 1) := by
    ext <;> simp
  rw [hdecomp, map_add, map_smul, hz1] at hz2
  have hzero : L (0, 0) = 0 := map_zero L
  rw [hzero, zero_add] at hz2
  exact (smul_eq_zero.mp hz2).resolve_right hL

private lemma triangularContinuousLinearMapGeneral_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (E × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    Function.Surjective (triangularContinuousLinearMapGeneral L) := by
  intro z
  let y : ℝ := (z.2 - L (z.1, 0)) / L (0, 1)
  refine ⟨(z.1, y), ?_⟩
  apply Prod.ext
  · rfl
  · change L (z.1, y) = z.2
    have hdecomp : (z.1, y) = (z.1, 0) + y • (0, 1) := by
      ext <;> simp
    rw [hdecomp, map_add, map_smul]
    dsimp [y]
    field_simp [hL]
    ring

private noncomputable def triangularContinuousLinearEquivGeneral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (L : (E × ℝ) →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) :=
  ContinuousLinearEquiv.ofBijective (triangularContinuousLinearMapGeneral L)
    (LinearMap.ker_eq_bot.mpr
      (triangularContinuousLinearMapGeneral_injective L hL))
    (LinearMap.range_eq_top.mpr
      (triangularContinuousLinearMapGeneral_surjective L hL))

private lemma fderiv_fst_prod_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E × ℝ → ℝ} {u : E × ℝ} (hp : DifferentiableAt ℝ p u) :
    fderiv ℝ (fun z : E × ℝ ↦ (z.1, p z)) u =
      triangularContinuousLinearMapGeneral (fderiv ℝ p u) := by
  rw [differentiableAt_fst.fderiv_prodMk hp, fderiv_fst]
  rfl

private theorem exists_open_implicit_unique_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : E × ℝ → ℝ} {u : E × ℝ} (hp : AnalyticAt ℝ p u)
    (hpartial : fderiv ℝ p u (0, 1) ≠ 0) :
    ∃ S : Set (E × ℝ), IsOpen S ∧ u ∈ S ∧
      Set.InjOn (fun z : E × ℝ ↦ (z.1, p z)) S := by
  let H : E × ℝ → E × ℝ := fun z ↦ (z.1, p z)
  have hH : AnalyticAt ℝ H u := analyticAt_fst.prod hp
  let i : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    triangularContinuousLinearEquivGeneral (fderiv ℝ p u) hpartial
  have hi : fderiv ℝ H u = (i : (E × ℝ) →L[ℝ] (E × ℝ)) := by
    rw [fderiv_fst_prod_general hp.differentiableAt]
    rfl
  let hs := strictFDerivOfAnalyticEquiv hH i hi
  let R := hs.toOpenPartialHomeomorph H
  refine ⟨R.source, R.open_source, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  simpa [R, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using R.injOn

private theorem exists_analytic_implicit_branch_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {p : E × ℝ → ℝ} {u : E × ℝ} (hp : AnalyticAt ℝ p u)
    (hpartial : fderiv ℝ p u (0, 1) ≠ 0) :
    ∃ ψ : E → ℝ,
      AnalyticAt ℝ ψ u.1 ∧ ψ u.1 = u.2 ∧
        ∀ᶠ z in nhds u.1, p (z, ψ z) = p u := by
  let H : E × ℝ → E × ℝ := fun z ↦ (z.1, p z)
  have hH : AnalyticAt ℝ H u := analyticAt_fst.prod hp
  let i : (E × ℝ) ≃L[ℝ] (E × ℝ) :=
    triangularContinuousLinearEquivGeneral (fderiv ℝ p u) hpartial
  have hi : fderiv ℝ H u = (i : (E × ℝ) →L[ℝ] (E × ℝ)) := by
    rw [fderiv_fst_prod_general hp.differentiableAt]
    rfl
  let r : E × ℝ → E × ℝ := analyticLocalInverse hH i hi
  let ψ : E → ℝ := fun z ↦ (r (z, p u)).2
  refine ⟨ψ, ?_, ?_, ?_⟩
  · have hpair : AnalyticAt ℝ (fun z : E ↦ (z, p u)) u.1 :=
      analyticAt_id.prod analyticAt_const
    have hr : AnalyticAt ℝ r (H u) := analyticAt_analyticLocalInverse hH i hi
    have hcomp : AnalyticAt ℝ (fun z : E ↦ r (z, p u)) u.1 := by
      have hc := hr.comp_of_eq hpair (by simp [H])
      change AnalyticAt ℝ (fun z : E ↦ r (z, p u)) u.1 at hc
      exact hc
    exact analyticAt_snd.comp hcomp
  · have hinv := analyticLocalInverse_apply hH i hi
    exact congrArg Prod.snd hinv
  · have hright := eventually_apply_analyticLocalInverse hH i hi
    have hpair : Filter.Tendsto (fun z : E ↦ (z, p u))
        (nhds u.1) (nhds (H u)) := by
      simpa [H] using
        (analyticAt_id.prod analyticAt_const :
          AnalyticAt ℝ (fun z : E ↦ (z, p u)) u.1).continuousAt.tendsto
    filter_upwards [hpair.eventually hright] with z hz
    have hz1 := congrArg Prod.fst hz
    have hz2 := congrArg Prod.snd hz
    change (r (z, p u)).1 = z at hz1
    change p (r (z, p u)) = p u at hz2
    change p (z, (r (z, p u)).2) = p u
    rw [show (z, (r (z, p u)).2) = r (z, p u) from Prod.ext hz1.symm rfl]
    exact hz2

private theorem exists_rational_product_box_subset_open {k : ℕ}
    (u : Fin k → ℝ) (x : ℝ) {S : Set ((Fin k → ℝ) × ℝ)}
    (hSopen : IsOpen S) (hmem : (u, x) ∈ S) :
    ∃ input : Fin k → ℚ × ℚ, ∃ output : ℚ × ℚ,
      (∀ j, inRationalInterval (input j) (u j)) ∧
        inRationalInterval output x ∧
        ∀ v y, (∀ j, inRationalInterval (input j) (v j)) →
          inRationalInterval output y → (v, y) ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSopen (u, x) hmem
  choose a ha using fun j : Fin k ↦
    exists_rat_btwn (sub_lt_self (u j) hε)
  choose b hb using fun j : Fin k ↦
    exists_rat_btwn (lt_add_of_pos_right (u j) hε)
  obtain ⟨c, hc1, hc2⟩ := exists_rat_btwn (sub_lt_self x hε)
  obtain ⟨d, hd1, hd2⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
  refine ⟨fun j ↦ (a j, b j), (c, d), ?_, ?_, ?_⟩
  · intro j
    exact ⟨(ha j).2, (hb j).1⟩
  · exact ⟨hc2, hd1⟩
  · intro v y hv hy
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_pi_lt_iff hε]
      intro j
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> dsimp [inRationalInterval] at hv <;>
        linarith [(ha j).1, (hv j).1, (hv j).2, (hb j).2]
    · rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> dsimp [inRationalInterval] at hy <;>
        linarith [hc1, hy.1, hy.2, hd2]

private theorem exists_rational_pi_product_box_subset_open {k n : ℕ}
    (u : Fin k → ℝ) (x : Fin n → ℝ)
    {S : Set ((Fin k → ℝ) × (Fin n → ℝ))}
    (hSopen : IsOpen S) (hmem : (u, x) ∈ S) :
    ∃ input : Fin k → ℚ × ℚ, ∃ output : Fin n → ℚ × ℚ,
      (∀ j, inRationalInterval (input j) (u j)) ∧
        (∀ i, inRationalInterval (output i) (x i)) ∧
        ∀ v y, (∀ j, inRationalInterval (input j) (v j)) →
          (∀ i, inRationalInterval (output i) (y i)) → (v, y) ∈ S := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSopen (u, x) hmem
  choose a ha using fun j : Fin k ↦
    exists_rat_btwn (sub_lt_self (u j) hε)
  choose b hb using fun j : Fin k ↦
    exists_rat_btwn (lt_add_of_pos_right (u j) hε)
  choose c hc using fun i : Fin n ↦
    exists_rat_btwn (sub_lt_self (x i) hε)
  choose d hd using fun i : Fin n ↦
    exists_rat_btwn (lt_add_of_pos_right (x i) hε)
  refine ⟨fun j ↦ (a j, b j), fun i ↦ (c i, d i), ?_, ?_, ?_⟩
  · intro j
    exact ⟨(ha j).2, (hb j).1⟩
  · intro i
    exact ⟨(hc i).2, (hd i).1⟩
  · intro v y hv hy
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · rw [dist_pi_lt_iff hε]
      intro j
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> dsimp [inRationalInterval] at hv <;>
        linarith [(ha j).1, (hv j).1, (hv j).2, (hb j).2]
    · rw [dist_pi_lt_iff hε]
      intro i
      rw [Real.dist_eq, abs_sub_lt_iff]
      constructor <;> dsimp [inRationalInterval] at hy <;>
        linarith [(hc i).1, (hy i).1, (hy i).2, (hd i).2]

private theorem exists_rational_pi_box_subset_open {k : ℕ}
    (u : Fin k → ℝ) {S : Set (Fin k → ℝ)}
    (hSopen : IsOpen S) (hmem : u ∈ S) :
    ∃ input : Fin k → ℚ × ℚ,
      (∀ j, inRationalInterval (input j) (u j)) ∧
        ∀ v, (∀ j, inRationalInterval (input j) (v j)) → v ∈ S := by
  let T : Set ((Fin k → ℝ) × (Fin 0 → ℝ)) := Prod.fst ⁻¹' S
  have hTopen : IsOpen T := hSopen.preimage continuous_fst
  have hTmem : (u, fun i : Fin 0 ↦ i.elim0) ∈ T := hmem
  obtain ⟨input, output, hu, _, hsub⟩ :=
    exists_rational_pi_product_box_subset_open u (fun i : Fin 0 ↦ i.elim0)
      hTopen hTmem
  refine ⟨input, hu, ?_⟩
  intro v hv
  have h := hsub v (fun i : Fin 0 ↦ i.elim0) hv (fun i ↦ i.elim0)
  exact h

private theorem analyticAt_chartValue_update
    {n : ℕ} (c : AlgebraicChartCode n) (u : Fin c.1 → ℝ)
    (i : Fin n) (j : Fin c.1) (hbox : chartInputBox c u)
    (hunique : ∀ v, chartInputBox c v → ∃! y, chartRoot c v i y)
    (hpartial :
      fderiv ℝ
        (fun z : ℝ × ℝ ↦
          evalChartPolynomial (c.2.1 i) (Function.update u j z.1) z.2)
        (u j, chartValue c u i) (0, 1) ≠ 0) :
    AnalyticAt ℝ
      (fun z : ℝ ↦ chartValue c (Function.update u j z) i) (u j) := by
  let y : ℝ := chartValue c u i
  let p : ℝ × ℝ → ℝ := fun z ↦
    evalChartPolynomial (c.2.1 i) (Function.update u j z.1) z.2
  have hinput : AnalyticAt ℝ
      (fun z : ℝ × ℝ ↦ Function.update u j z.1) (u j, y) := by
    apply AnalyticAt.pi
    intro l
    simp only [Function.update]
    split_ifs
    ·
      simpa using (analyticAt_fst :
        AnalyticAt ℝ (fun z : ℝ × ℝ ↦ z.1) (u j, y))
    ·
      exact analyticAt_const
  have hmap : AnalyticAt ℝ
      (fun z : ℝ × ℝ ↦ (Function.update u j z.1, z.2)) (u j, y) :=
    hinput.prod analyticAt_snd
  have hp : AnalyticAt ℝ p (u j, y) := by
    have hfull := analyticAt_evalChartPolynomial (c.2.1 i) (u, y)
    apply hfull.comp_of_eq hmap
    apply Prod.ext
    · funext l
      simp
    · rfl
  have hpartial' : fderiv ℝ p (u j, y) (0, 1) ≠ 0 := by
    simpa only [p, y] using hpartial
  obtain ⟨ψ, hψ, hψcenter, hψrel⟩ :=
    exists_analytic_implicit_branch hp hpartial'
  have huUnique : ∃! z, chartRoot c u i z := hunique u hbox
  have hyRoot : chartRoot c u i y := by
    simpa only [y] using chartValue_root c u i huUnique
  have hpzero : p (u j, y) = 0 := by
    change evalChartPolynomial (c.2.1 i) (Function.update u j (u j)) y = 0
    rw [show Function.update u j (u j) = u by
      funext l
      simp only [Function.update]
      split_ifs with h
      · subst l
        rfl
      · rfl]
    exact hyRoot.2
  have hinputEventually :
      ∀ᶠ z in nhds (u j), chartInputBox c (Function.update u j z) := by
    have hj : ∀ᶠ z in nhds (u j),
        inRationalInterval (c.2.2.1 j) z := by
      change Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ) ∈ nhds (u j)
      exact Ioo_mem_nhds (hbox j).1 (hbox j).2
    filter_upwards [hj] with z hz
    intro l
    by_cases hlj : l = j
    · subst l
      simpa using hz
    · change inRationalInterval (c.2.2.1 l) ((Function.update u j z) l)
      rw [Function.update]
      split
      · rename_i h
        exact (hlj h).elim
      · exact hbox l
  have houtputEventually : ∀ᶠ z in nhds (u j),
      inRationalInterval (c.2.2.2 i) (ψ z) := by
    change {z | ψ z ∈
      Set.Ioo ((c.2.2.2 i).1 : ℝ) ((c.2.2.2 i).2 : ℝ)} ∈ nhds (u j)
    apply hψ.continuousAt
    rw [hψcenter]
    exact Ioo_mem_nhds hyRoot.1.1 hyRoot.1.2
  have heq : ψ =ᶠ[nhds (u j)]
      (fun z ↦ chartValue c (Function.update u j z) i) := by
    filter_upwards [hinputEventually, houtputEventually, hψrel] with z hzbox hzout hzrel
    have hzpoly :
        evalChartPolynomial (c.2.1 i) (Function.update u j z) (ψ z) = 0 := by
      change p (z, ψ z) = 0
      rw [hzrel, hpzero]
    have hzroot : chartRoot c (Function.update u j z) i (ψ z) :=
      ⟨hzout, hzpoly⟩
    exact (chartValue_eq_of_root c (Function.update u j z) i
      (hunique _ hzbox) hzroot).symm
  exact hψ.congr heq

private theorem isAlgebraicAnalyticAtOver_chartValue_update
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {n : ℕ} (c : AlgebraicChartCode n) (u : Fin c.1 → ℝ)
    (i : Fin n) (j : Fin c.1) (fixed : Fin c.1 → K)
    (hfixed : ∀ l, l ≠ j → algebraMap K ℝ (fixed l) = u l)
    (hbox : chartInputBox c u)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hpartial :
      evalChartPolynomial (c.2.1 i).derivative u (chartValue c u i) ≠ 0) :
    IsAlgebraicAnalyticAtOver K
      (fun z ↦ chartValue c (Function.update u j z) i) (u j) := by
  let P := c.2.1 i
  let y := chartValue c u i
  have hp : AnalyticAt ℝ
      (fun z : (Fin c.1 → ℝ) × ℝ ↦ evalChartPolynomial P z.1 z.2)
      (u, y) := analyticAt_evalChartPolynomial P (u, y)
  have hpvert :
      fderiv ℝ
        (fun z : (Fin c.1 → ℝ) × ℝ ↦ evalChartPolynomial P z.1 z.2)
        (u, y) (0, 1) ≠ 0 := by
    rw [fderiv_evalChartPolynomial_vertical]
    exact hpartial
  obtain ⟨ψ, hψan, hψcenter, hψroot⟩ :=
    exists_analytic_implicit_branch_general hp hpvert
  have hupdateAn : AnalyticAt ℝ
      (fun z : ℝ ↦ Function.update u j z) (u j) := by
    apply AnalyticAt.pi
    intro l
    by_cases hlj : l = j
    · subst l
      convert (analyticAt_id : AnalyticAt ℝ id (u j)) using 1
      funext z
      simp [Function.update]
    · simpa [Function.update, hlj] using
        (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ u l) (u j))
  have hbranchAn : AnalyticAt ℝ
      (fun z ↦ ψ (Function.update u j z)) (u j) := by
    apply hψan.comp_of_eq hupdateAn
    funext l
    simp
  have hinputEventually : ∀ᶠ z in nhds (u j),
      chartInputBox c (Function.update u j z) := by
    have hj : ∀ᶠ z in nhds (u j),
        inRationalInterval (c.2.2.1 j) z := by
      change Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ) ∈ nhds (u j)
      exact Ioo_mem_nhds (hbox j).1 (hbox j).2
    filter_upwards [hj] with z hz
    intro l
    by_cases hlj : l = j
    · subst l
      simpa using hz
    · simpa [Function.update, hlj] using hbox l
  have hbranchEq :
      (fun z ↦ ψ (Function.update u j z)) =ᶠ[nhds (u j)]
        (fun z ↦ chartValue c (Function.update u j z) i) := by
    have hrootEventually : ∀ᶠ v in nhds u,
        evalChartPolynomial P v (ψ v) = 0 := by
      filter_upwards [hψroot] with v hv
      rw [hv]
      have hu : ∃! z, chartRoot c u i z := hunique u hbox i
      exact (chartValue_root c u i hu).2
    have htend : Filter.Tendsto (fun z ↦ Function.update u j z)
        (nhds (u j)) (nhds u) := by
      simpa using hupdateAn.continuousAt.tendsto
    have hrootUpdate := htend.eventually hrootEventually
    have hcenter : ψ u = y := hψcenter
    have hout : ∀ᶠ v in nhds u,
        inRationalInterval (c.2.2.2 i) (ψ v) := by
      change ψ ⁻¹' Set.Ioo ((c.2.2.2 i).1 : ℝ)
          ((c.2.2.2 i).2 : ℝ) ∈ nhds u
      apply hψan.continuousAt
      rw [hcenter]
      have hyroot : chartRoot c u i y := by
        simpa only [y] using chartValue_root c u i (hunique u hbox i)
      exact Ioo_mem_nhds hyroot.1.1 hyroot.1.2
    have houtUpdate := htend.eventually hout
    filter_upwards [hinputEventually, hrootUpdate, houtUpdate] with z hzbox hzroot hzout
    have hzRoot : chartRoot c (Function.update u j z) i
        (ψ (Function.update u j z)) := ⟨hzout, hzroot⟩
    exact (chartValue_eq_of_root c _ i (hunique _ hzbox i) hzRoot).symm
  have han : AnalyticAt ℝ
      (fun z ↦ chartValue c (Function.update u j z) i) (u j) :=
    hbranchAn.congr hbranchEq
  let Q : Polynomial (Polynomial K) :=
    specializeChartPolynomial fixed j P
  have hfixedUpdate (z : ℝ) :
      Function.update (fun l ↦ algebraMap K ℝ (fixed l)) j z =
        Function.update u j z := by
    funext l
    by_cases hlj : l = j
    · subst l
      simp
    · simp [Function.update, hlj, hfixed l hlj]
  have hQne : Q ≠ 0 := by
    intro hQ
    have hQderiv : specializeChartPolynomial fixed j P.derivative = 0 := by
      rw [specializeChartPolynomial_derivative]
      change Q.derivative = 0
      rw [hQ, Polynomial.derivative_zero]
    have hev := congrArg
      (fun R : Polynomial (Polynomial K) ↦
        evalBivariateOver R (u j) (chartValue c u i)) hQderiv
    simp only [evalBivariateOver, Polynomial.eval₂_zero] at hev
    change evalBivariateOver (specializeChartPolynomial fixed j P.derivative)
        (u j) (chartValue c u i) = 0 at hev
    rw [eval_specializeChartPolynomial, hfixedUpdate] at hev
    have huUpdate : Function.update u j (u j) = u := by
      funext l
      by_cases hlj : l = j
      · subst l
        simp
      · simp [Function.update, hlj]
    rw [huUpdate] at hev
    exact hpartial hev
  refine ⟨han, Q, hQne, ?_⟩
  filter_upwards [hinputEventually] with z hzbox
  rw [show evalBivariateOver Q z
      (chartValue c (Function.update u j z) i) =
        evalChartPolynomial P (Function.update u j z)
          (chartValue c (Function.update u j z) i) by
    rw [show Q = specializeChartPolynomial fixed j P by rfl,
      eval_specializeChartPolynomial, hfixedUpdate]]
  exact (chartValue_root c _ i (hunique _ hzbox i)).2

private theorem chartValue_isAlgebraic_of_parameters
    {K : Type*} [Field K] [Algebra RealAlgebraic K] [Algebra K ℝ]
    [IsScalarTower RealAlgebraic K ℝ]
    {n : ℕ} (c : AlgebraicChartCode n) (u : Fin c.1 → ℝ)
    (i : Fin n) (fixed : Fin c.1 → K)
    (hfixed : ∀ l, algebraMap K ℝ (fixed l) = u l)
    (hbox : chartInputBox c u)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hpartial :
      evalChartPolynomial (c.2.1 i).derivative u (chartValue c u i) ≠ 0) :
    IsAlgebraic K (chartValue c u i) := by
  let P := c.2.1 i
  let Q : Polynomial K := specializeAllChartPolynomial fixed P
  have hQne : Q ≠ 0 := by
    intro hQ
    have hQderiv : specializeAllChartPolynomial fixed P.derivative = 0 := by
      rw [specializeAllChartPolynomial_derivative]
      change Q.derivative = 0
      rw [hQ, Polynomial.derivative_zero]
    have hev := congrArg
      (fun R : Polynomial K ↦ R.eval₂ (algebraMap K ℝ) (chartValue c u i))
      hQderiv
    simp only [Polynomial.eval₂_zero] at hev
    rw [eval_specializeAllChartPolynomial] at hev
    have hfun : (fun l ↦ algebraMap K ℝ (fixed l)) = u := by
      funext l
      exact hfixed l
    rw [hfun] at hev
    exact hpartial hev
  refine ⟨Q, hQne, ?_⟩
  rw [Polynomial.aeval_def]
  rw [show Q = specializeAllChartPolynomial fixed P by rfl,
    eval_specializeAllChartPolynomial]
  have hfun : (fun l ↦ algebraMap K ℝ (fixed l)) = u := by
    funext l
    exact hfixed l
  rw [hfun]
  exact (chartValue_root c u i (hunique u hbox i)).2

private def IsPointAlgebraicChart {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∃ hcard : c.1 = (pointTranscendenceSupport x).card,
    let u : Fin c.1 → ℝ := fun j ↦ pointSupportTuple x (Fin.cast hcard j)
    chartInputBox c u ∧
      (∀ v, chartInputBox c v → StrictMono v) ∧
      (∀ i, chartValue c u i = x i) ∧
      (∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y) ∧
      ∀ v, chartInputBox c v → ∀ i,
        evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0

private theorem isOpen_strictMono_fin {k : ℕ} :
    IsOpen {v : Fin k → ℝ | StrictMono v} := by
  rw [show {v : Fin k → ℝ | StrictMono v} =
      ⋂ i : Fin k, ⋂ j : Fin k, ⋂ (_h : i < j), {v | v i < v j} by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact Iff.rfl]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_lt (continuous_apply i) (continuous_apply j)

private theorem pointSupportTuple_strictMono {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : StrictMono (pointSupportTuple x) := by
  intro i j hij
  exact ((pointTranscendenceSupport x).orderEmbOfFin rfl).strictMono hij

private theorem exists_point_algebraicChartCode {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ c : AlgebraicChartCode n, IsPointAlgebraicChart c x := by
  classical
  let k := (pointTranscendenceSupport x).card
  let u : Fin k → ℝ := pointSupportTuple x
  obtain ⟨P, hP⟩ := exists_point_chart_polynomials x
  have hp (i : Fin n) : AnalyticAt ℝ
      (fun z : (Fin k → ℝ) × ℝ ↦ evalChartPolynomial (P i) z.1 z.2)
      (u, x i) := analyticAt_evalChartPolynomial (P i) (u, x i)
  have hpartial (i : Fin n) :
      fderiv ℝ
        (fun z : (Fin k → ℝ) × ℝ ↦ evalChartPolynomial (P i) z.1 z.2)
        (u, x i) (0, 1) ≠ 0 := by
    rw [fderiv_evalChartPolynomial_vertical]
    exact (hP i).2
  choose S hS using fun i : Fin n ↦
    exists_open_implicit_unique_source (hp i) (hpartial i)
  choose sourceInput output hsourceBox using fun i : Fin n ↦
    exists_rational_product_box_subset_open u (x i) (hS i).1 (hS i).2.1
  choose ψ hψ using fun i : Fin n ↦
    exists_analytic_implicit_branch_general (hp i) (hpartial i)
  let Good : (Fin k → ℝ) → Prop := fun v ↦ ∀ i : Fin n,
    (∀ j, inRationalInterval (sourceInput i j) (v j)) ∧
      inRationalInterval (output i) (ψ i v) ∧
      evalChartPolynomial (P i) v (ψ i v) = 0 ∧
      evalChartPolynomial (P i).derivative v (ψ i v) ≠ 0
  have hGoodEventually : ∀ᶠ v in nhds u, Good v := by
    apply Filter.eventually_all.mpr
    intro i
    have hinput : ∀ᶠ v in nhds u,
        ∀ j, inRationalInterval (sourceInput i j) (v j) := by
      apply Filter.eventually_all.mpr
      intro j
      change (fun v : Fin k → ℝ ↦ v j) ⁻¹'
          Set.Ioo (((sourceInput i j).1 : ℚ) : ℝ)
            (((sourceInput i j).2 : ℚ) : ℝ) ∈ nhds u
      exact (continuous_apply j).continuousAt
        (Ioo_mem_nhds ((hsourceBox i).1 j).1 ((hsourceBox i).1 j).2)
    have houtput : ∀ᶠ v in nhds u,
        inRationalInterval (output i) (ψ i v) := by
      change (fun v ↦ ψ i v) ⁻¹'
          Set.Ioo (((output i).1 : ℚ) : ℝ) (((output i).2 : ℚ) : ℝ) ∈ nhds u
      apply (hψ i).1.continuousAt
      rw [(hψ i).2.1]
      exact Ioo_mem_nhds ((hsourceBox i).2.1).1 ((hsourceBox i).2.1).2
    have hroot : ∀ᶠ v in nhds u,
        evalChartPolynomial (P i) v (ψ i v) = 0 := by
      filter_upwards [(hψ i).2.2] with v hv
      rw [hv]
      exact (hP i).1
    have hpair : AnalyticAt ℝ (fun v : Fin k → ℝ ↦ (v, ψ i v)) u :=
      analyticAt_id.prod (hψ i).1
    have hderivAnalytic : AnalyticAt ℝ
        (fun v : Fin k → ℝ ↦
          evalChartPolynomial (P i).derivative v (ψ i v)) u := by
      apply (analyticAt_evalChartPolynomial (P i).derivative (u, x i)).comp_of_eq hpair
      rw [(hψ i).2.1]
    have hderivCenter :
        evalChartPolynomial (P i).derivative u (ψ i u) ≠ 0 := by
      rw [(hψ i).2.1]
      simpa only [u, k] using (hP i).2
    have hderiv : ∀ᶠ v in nhds u,
        evalChartPolynomial (P i).derivative v (ψ i v) ≠ 0 :=
      hderivAnalytic.continuousAt.eventually_ne hderivCenter
    filter_upwards [hinput, houtput, hroot, hderiv] with v hvIn hvOut hvRoot hvDeriv
    exact ⟨hvIn, hvOut, hvRoot, hvDeriv⟩
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_nhds_iff.mp hGoodEventually
  obtain ⟨input, huInput, hinputSub⟩ :=
    exists_rational_pi_box_subset_open u
      (hVopen.inter isOpen_strictMono_fin)
      ⟨huV, pointSupportTuple_strictMono x⟩
  let c : AlgebraicChartCode n := ⟨k, P, input, output⟩
  have hbox : chartInputBox c u := huInput
  have hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y := by
    intro v hv i
    have hvV : v ∈ V := (hinputSub v hv).1
    have hgood := hVsub hvV i
    have hψRoot : chartRoot c v i (ψ i v) := ⟨hgood.2.1, hgood.2.2.1⟩
    refine ⟨ψ i v, hψRoot, ?_⟩
    intro y hy
    have hψS : (v, ψ i v) ∈ S i :=
      (hsourceBox i).2.2 v (ψ i v) hgood.1 hgood.2.1
    have hyS : (v, y) ∈ S i :=
      (hsourceBox i).2.2 v y hgood.1 hy.1
    have heq := (hS i).2.2 hψS hyS
      (Prod.ext rfl (hgood.2.2.1.trans hy.2.symm))
    exact (congrArg Prod.snd heq).symm
  refine ⟨c, rfl, ?_⟩
  dsimp only [Fin.cast_refl]
  refine ⟨hbox, (fun v hv ↦ (hinputSub v hv).2), ?_, hunique, ?_⟩
  · intro i
    have hxRoot : chartRoot c u i (x i) := by
      exact ⟨(hsourceBox i).2.1, (hP i).1⟩
    exact chartValue_eq_of_root c u i (hunique u hbox i) hxRoot
  · intro v hv i
    have hgood := hVsub (hinputSub v hv).1 i
    have hval : chartValue c v i = ψ i v :=
      chartValue_eq_of_root c v i (hunique v hv i)
        ⟨hgood.2.1, hgood.2.2.1⟩
    rw [hval]
    exact hgood.2.2.2

private noncomputable def pointAlgebraicChartCode {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : AlgebraicChartCode n :=
  (exists_point_algebraicChartCode x).choose

private theorem pointAlgebraicChartCode_spec {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    IsPointAlgebraicChart (pointAlgebraicChartCode x) x :=
  (exists_point_algebraicChartCode x).choose_spec

private noncomputable def pointChartCardEq {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    (pointAlgebraicChartCode x).1 = (pointTranscendenceSupport x).card :=
  (pointAlgebraicChartCode_spec x).choose

private noncomputable def pointChartParameters {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Fin (pointAlgebraicChartCode x).1 → ℝ :=
  fun j ↦ pointSupportTuple x (Fin.cast (pointChartCardEq x) j)

private noncomputable def pointChartSupportIndex {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Fin (pointAlgebraicChartCode x).1 → RealTranscendenceBasisIndex :=
  fun j ↦ (pointTranscendenceSupport x).orderEmbOfFin rfl
    (Fin.cast (pointChartCardEq x) j)

private theorem pointChartParameters_eq_basisValue {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin (pointAlgebraicChartCode x).1) :
    pointChartParameters x j =
      realTranscendenceBasisValue (pointChartSupportIndex x j) := rfl

private theorem pointChartSupportIndex_mem {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin (pointAlgebraicChartCode x).1) :
    pointChartSupportIndex x j ∈ pointTranscendenceSupport x :=
  Finset.orderEmbOfFin_mem _ _ _

private theorem pointChartSupportIndex_injective {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Function.Injective (pointChartSupportIndex x) := by
  intro a b hab
  apply (Fin.castOrderIso (pointChartCardEq x)).injective
  exact ((pointTranscendenceSupport x).orderEmbOfFin rfl).injective hab

private theorem pointChartParameters_input {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    chartInputBox (pointAlgebraicChartCode x) (pointChartParameters x) := by
  change chartInputBox (pointAlgebraicChartCode x)
    (fun j ↦ pointSupportTuple x
      (Fin.cast (pointAlgebraicChartCode_spec x).choose j))
  exact (pointAlgebraicChartCode_spec x).choose_spec.1

private theorem pointChartParameters_value {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    chartValue (pointAlgebraicChartCode x) (pointChartParameters x) i = x i := by
  change chartValue (pointAlgebraicChartCode x)
    (fun j ↦ pointSupportTuple x
      (Fin.cast (pointAlgebraicChartCode_spec x).choose j)) i = x i
  exact (pointAlgebraicChartCode_spec x).choose_spec.2.2.1 i

private theorem pointChartParameters_strictMono {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : StrictMono (pointChartParameters x) := by
  exact (pointAlgebraicChartCode_spec x).choose_spec.2.1 _
    (pointChartParameters_input x)

private theorem pointChartParameters_unique {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ v, chartInputBox (pointAlgebraicChartCode x) v →
      ∀ i, ∃! y, chartRoot (pointAlgebraicChartCode x) v i y := by
  exact (pointAlgebraicChartCode_spec x).choose_spec.2.2.2.1

private theorem pointChartParameters_derivative {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ∀ v, chartInputBox (pointAlgebraicChartCode x) v → ∀ i,
      evalChartPolynomial ((pointAlgebraicChartCode x).2.1 i).derivative v
        (chartValue (pointAlgebraicChartCode x) v i) ≠ 0 := by
  exact (pointAlgebraicChartCode_spec x).choose_spec.2.2.2.2

private theorem pointChartParameters_range {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    Set.range (pointChartParameters x) =
      realTranscendenceBasisValue ''
        (pointTranscendenceSupport x : Set RealTranscendenceBasisIndex) := by
  rw [← range_pointSupportTuple]
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast (pointChartCardEq x) j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨Fin.cast (pointChartCardEq x).symm j, ?_⟩
    simp [pointChartParameters]

private theorem exists_chartCurve_point_ne {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n))
    (j : Fin (pointAlgebraicChartCode x).1) :
    ∃ z : ℝ,
      inRationalInterval ((pointAlgebraicChartCode x).2.2.1 j) z ∧
      chartPoint (pointAlgebraicChartCode x)
          (Function.update (pointChartParameters x) j z) ≠ x := by
  classical
  let c := pointAlgebraicChartCode x
  let u := pointChartParameters x
  let t := pointChartSupportIndex x j
  let q : ℚ :=
    (((pointAlgebraicChartCode x).2.2.1 j).1 +
      ((pointAlgebraicChartCode x).2.2.1 j).2) / 2
  let z : ℝ := (q : ℝ)
  have hjbox := pointChartParameters_input x j
  have hz : inRationalInterval ((pointAlgebraicChartCode x).2.2.1 j) z := by
    have habR :
        (((pointAlgebraicChartCode x).2.2.1 j).1 : ℝ) <
          (((pointAlgebraicChartCode x).2.2.1 j).2 : ℝ) :=
      hjbox.1.trans hjbox.2
    have habQ :
        ((pointAlgebraicChartCode x).2.2.1 j).1 <
          ((pointAlgebraicChartCode x).2.2.1 j).2 := by
      exact_mod_cast habR
    have hlo : ((pointAlgebraicChartCode x).2.2.1 j).1 < q := by
      dsimp only [q]
      linarith
    have hhi : q < ((pointAlgebraicChartCode x).2.2.1 j).2 := by
      dsimp only [q]
      linarith
    dsimp only [inRationalInterval, z]
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  have hupdatedBox : chartInputBox c (Function.update u j z) := by
    intro l
    by_cases hlj : l = j
    · subst l
      simpa [c, u, Function.update] using hz
    · simpa [c, u, Function.update, hlj] using pointChartParameters_input x l
  let fixed : Fin c.1 → PivotBaseField t := fun l ↦
    if hlj : l = j then algebraMap ℚ (PivotBaseField t) q
    else basisValueInPivotBaseField t (pointChartSupportIndex x l)
      ((pointChartSupportIndex_injective x).ne hlj)
  have hfixed : ∀ l,
      algebraMap (PivotBaseField t) ℝ (fixed l) =
        Function.update u j z l := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [fixed, z, Function.update,
        IsScalarTower.algebraMap_apply ℚ (PivotBaseField t) ℝ]
    · rw [show fixed l = basisValueInPivotBaseField t
          (pointChartSupportIndex x l)
          ((pointChartSupportIndex_injective x).ne hlj) by
        simp [fixed, hlj]]
      change realTranscendenceBasisValue (pointChartSupportIndex x l) =
        Function.update u j z l
      simp [Function.update, hlj, u, pointChartParameters_eq_basisValue]
  refine ⟨z, hz, ?_⟩
  intro heq
  have hxalg : ∀ i : Fin n, IsAlgebraic (PivotBaseField t) (x i) := by
    intro i
    have halg : IsAlgebraic (PivotBaseField t)
        (chartValue c (Function.update u j z) i) :=
      chartValue_isAlgebraic_of_parameters c (Function.update u j z) i fixed
        hfixed hupdatedBox (by
          simpa only [c] using pointChartParameters_unique x)
        (by
          simpa only [c] using
            pointChartParameters_derivative x (Function.update u j z)
              hupdatedBox i)
    have hei := congrArg (fun p : EuclideanSpace ℝ (Fin n) ↦ p i) heq
    change chartValue c (Function.update u j z) i = x i at hei
    rwa [hei] at halg
  have hminimal := pointTranscendenceSupport_minimal x
    (S := realTranscendenceBasisValue ''
      ({t}ᶜ : Set RealTranscendenceBasisIndex))
    (by
      rintro _ ⟨s, _, rfl⟩
      exact s.2)
    (fun i ↦ (IntermediateField.isAlgebraic_adjoin_iff).mp (hxalg i))
  have htmem : realTranscendenceBasisValue t ∈
      realTranscendenceBasisValue ''
        ({t}ᶜ : Set RealTranscendenceBasisIndex) :=
    hminimal ⟨t, pointChartSupportIndex_mem x j, rfl⟩
  obtain ⟨s, hst, heqst⟩ := htmem
  have : s = t := Subtype.ext heqst
  exact hst (by simpa [this])

/-! ### The CH finite-support fingerprint

Once the basis is well-ordered with countable initial segments, every finite support receives a
natural local code relative to its well-order maximum.  Equal fingerprints fix the support size
and the position of the selected maximum in the ordinary real order; if the selected maxima are
also equal, the entire supports are equal.  This is Schmerl's Lemma 2.3 specialized to `m = 1`.
-/

private def PredecessorBoundedFinsets {X : Type*} [LinearOrder X] (p : X) :=
  {s : Finset X // ∀ x ∈ s, x ≤ p}

private def predecessorBoundedToIic {X : Type*} [LinearOrder X] (p : X)
    (s : PredecessorBoundedFinsets p) : Finset (Set.Iic p) :=
  s.1.attach.map
    { toFun := fun x ↦ ⟨x.1, s.2 x.1 x.2⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : Set.Iic p ↦ z.1) h }

private theorem mem_predecessorBoundedToIic {X : Type*} [LinearOrder X]
    (p : X) (s : PredecessorBoundedFinsets p) (x : Set.Iic p) :
    x ∈ predecessorBoundedToIic p s ↔ x.1 ∈ s.1 := by
  constructor
  · intro hx
    simp only [predecessorBoundedToIic, Finset.mem_map] at hx
    obtain ⟨a, _, hax⟩ := hx
    have hva : (a.1 : X) = x.1 := congrArg Subtype.val hax
    simpa only [← hva] using a.2
  · intro hx
    simp only [predecessorBoundedToIic, Finset.mem_map]
    refine ⟨⟨x.1, hx⟩, by simp, ?_⟩
    exact Subtype.ext rfl

private theorem predecessorBoundedToIic_injective {X : Type*} [LinearOrder X]
    (p : X) : Function.Injective (predecessorBoundedToIic p) := by
  intro s t h
  apply Subtype.ext
  ext x
  by_cases hxp : x ≤ p
  · let xp : Set.Iic p := ⟨x, hxp⟩
    have hm := Finset.ext_iff.mp h xp
    simpa only [mem_predecessorBoundedToIic] using hm
  · constructor <;> intro hx
    · exact (hxp (s.2 x hx)).elim
    · exact (hxp (t.2 x hx)).elim

private theorem predecessorBoundedFinsets_countable
    {X : Type*} [LinearOrder X] {p : X} (hcount : Countable (Set.Iic p)) :
    Countable (PredecessorBoundedFinsets p) := by
  let : Countable (Set.Iic p) := hcount
  exact (predecessorBoundedToIic_injective p).countable

private noncomputable def predecessorBoundedCode
    {X : Type*} [LinearOrder X] (hcount : ∀ p : X, Countable (Set.Iic p))
    (p : X) : PredecessorBoundedFinsets p ↪ ℕ := by
  letI : Countable (PredecessorBoundedFinsets p) :=
    predecessorBoundedFinsets_countable (hcount p)
  letI : Encodable (PredecessorBoundedFinsets p) := Encodable.ofCountable _
  exact ⟨Encodable.encode, Encodable.encode_injective⟩

private def predecessorBoundedVersion {X : Type*} [LinearOrder X]
    (p : X) (s : Finset X) : PredecessorBoundedFinsets p :=
  ⟨s.filter (· ≤ p), fun _ hx ↦ (Finset.mem_filter.mp hx).2⟩

private noncomputable def localSupportCode {X : Type*} [LinearOrder X]
    (hcount : ∀ p : X, Countable (Set.Iic p)) (p : X) (s : Finset X) : ℕ :=
  predecessorBoundedCode hcount p (predecessorBoundedVersion p s)

private theorem localSupportCode_injective_of_bounded
    {X : Type*} [LinearOrder X]
    (hcount : ∀ p : X, Countable (Set.Iic p)) (p : X)
    {s t : Finset X} (hs : ∀ x ∈ s, x ≤ p) (ht : ∀ x ∈ t, x ≤ p)
    (hcode : localSupportCode hcount p s = localSupportCode hcount p t) : s = t := by
  have hbounded : predecessorBoundedVersion p s = predecessorBoundedVersion p t :=
    (predecessorBoundedCode hcount p).injective hcode
  have hval := congrArg Subtype.val hbounded
  simpa only [predecessorBoundedVersion, Finset.filter_eq_self.mpr hs,
    Finset.filter_eq_self.mpr ht] using hval

private abbrev SupportFingerprint := ℕ × ℕ × ℕ

private noncomputable def supportPosition {X : Type*} (ambient : X → ℝ)
    (p : X) (s : Finset X) : ℕ :=
  (s.filter fun x ↦ ambient x < ambient p).card

private noncomputable def supportFingerprint {X : Type*} [LinearOrder X]
    (hcount : ∀ p : X, Countable (Set.Iic p))
    (ambient : X → ℝ) (s : Finset X) : SupportFingerprint :=
  if hs : s.Nonempty then
    let p := s.max' hs
    (s.card, supportPosition ambient p s, localSupportCode hcount p s)
  else (0, 0, 0)

private theorem supportFingerprint_eq_imp {X : Type*} [LinearOrder X]
    {hcount : ∀ p : X, Countable (Set.Iic p)} {ambient : X → ℝ}
    {s t : Finset X} (hs : s.Nonempty) (ht : t.Nonempty)
    (hfp : supportFingerprint hcount ambient s = supportFingerprint hcount ambient t) :
    s.card = t.card ∧
      supportPosition ambient (s.max' hs) s = supportPosition ambient (t.max' ht) t ∧
      (s.max' hs = t.max' ht → s = t) := by
  simp [supportFingerprint, hs, ht] at hfp
  refine ⟨hfp.1, hfp.2.1, ?_⟩
  · intro hp
    have hcode := hfp.2.2
    rw [hp] at hcode
    exact localSupportCode_injective_of_bounded hcount (t.max' ht)
      (fun x hx ↦ hp ▸ Finset.le_max' s x hx)
      (fun x hx ↦ Finset.le_max' t x hx) hcode

/-! ## The Erdős--Kakutani construction on the real line

This section formalizes the dimension-one sufficiency theorem.  Under CH, order the indices of a
Hamel basis so that every proper initial segment is countable.  Color a nonzero real by its
largest support index and by a local natural-number code inside that (countable) support fiber.
Within one color, distinct vectors have distinct largest indices, so the usual triangular
argument proves linear independence over `ℚ`.
-/

private noncomputable def maxBasisIndex {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K V) (x : V) : ι := by
  classical
  exact if hx : x = 0 then Classical.arbitrary ι
    else (b.repr x).support.max' (by
      rw [Finsupp.support_nonempty_iff]
      simpa only [map_zero] using b.repr.injective.ne hx)

private theorem maxBasisIndex_mem {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K V)
    {x : V} (hx : x ≠ 0) : maxBasisIndex b x ∈ (b.repr x).support := by
  classical
  simp only [maxBasisIndex, dif_neg hx]
  exact Finset.max'_mem _ _

private theorem support_le_maxBasisIndex {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K V)
    {x : V} (hx : x ≠ 0) {i : ι} (hi : i ∈ (b.repr x).support) :
    i ≤ maxBasisIndex b x := by
  classical
  simp only [maxBasisIndex, dif_neg hx]
  exact Finset.le_max' _ _ hi

private theorem repr_at_maxBasisIndex_ne_zero {K V ι : Type*}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K V)
    {x : V} (hx : x ≠ 0) : b.repr x (maxBasisIndex b x) ≠ 0 :=
  Finsupp.mem_support_iff.mp (maxBasisIndex_mem b hx)

private theorem linearIndependent_of_injective_maxBasisIndex
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] [Nonempty ι] (b : Module.Basis ι K V)
    {J : Type*} (v : J → V) (hv0 : ∀ j, v j ≠ 0)
    (hpivot : Function.Injective (fun j ↦ maxBasisIndex b (v j))) :
    LinearIndependent K v := by
  classical
  let : LinearOrder J := LinearOrder.lift'
    (fun j ↦ maxBasisIndex b (v j)) hpivot
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  let active := s.filter (fun j ↦ g j ≠ 0)
  have hiactive : i ∈ active := by simp [active, hi, hgi]
  let j := active.max' ⟨i, hiactive⟩
  have hjactive : j ∈ active := Finset.max'_mem _ _
  have hj_s : j ∈ s := (Finset.mem_filter.mp hjactive).1
  have hgj : g j ≠ 0 := (Finset.mem_filter.mp hjactive).2
  have hcoord := congrArg (b.coord (maxBasisIndex b (v j))) hsum
  simp only [map_sum, map_smul, map_zero] at hcoord
  change (∑ q ∈ s, g q • b.repr (v q) (maxBasisIndex b (v j))) = 0 at hcoord
  have hoff : ∀ q ∈ s, q ≠ j →
      g q • b.repr (v q) (maxBasisIndex b (v j)) = 0 := by
    intro q hqs hqj
    by_cases hgq : g q = 0
    · simp [hgq]
    · have hqactive : q ∈ active := by simp [active, hqs, hgq]
      have hleJ : q ≤ j := Finset.le_max' active q hqactive
      have hle : maxBasisIndex b (v q) ≤ maxBasisIndex b (v j) := hleJ
      have hne : maxBasisIndex b (v q) ≠ maxBasisIndex b (v j) :=
        hpivot.ne hqj
      have hlt : maxBasisIndex b (v q) < maxBasisIndex b (v j) := hle.lt_of_ne hne
      have hnotmem : maxBasisIndex b (v j) ∉ (b.repr (v q)).support := by
        intro hmem
        have hsupport := support_le_maxBasisIndex b (hv0 q) hmem
        exact (not_le_of_gt hlt) hsupport
      rw [Finsupp.notMem_support_iff.mp hnotmem, smul_zero]
  have hsingle :
      ∑ q ∈ s, g q • b.repr (v q) (maxBasisIndex b (v j)) =
        g j • b.repr (v j) (maxBasisIndex b (v j)) := by
    rw [Finset.sum_eq_single j]
    · exact fun q hqs hqj ↦ hoff q hqs hqj
    · exact fun hjnot ↦ (hjnot hj_s).elim
  rw [hsingle] at hcoord
  exact (smul_ne_zero hgj (repr_at_maxBasisIndex_ne_zero b (hv0 j))) hcoord

private theorem exists_wellOrder_countable_Iio {X : Type*}
    (hX : Cardinal.mk X ≤ Cardinal.aleph 1) :
    ∃ (_ : LinearOrder X) (_ : WellFoundedLT X),
      ∀ x : X, (Set.Iio x).Countable := by
  obtain ⟨lo, wf, hord⟩ := Cardinal.exists_ord_eq_type_lt X
  refine ⟨lo, wf, ?_⟩
  intro x
  rw [← Cardinal.le_aleph0_iff_set_countable, ← Cardinal.lt_aleph_one_iff]
  exact (Cardinal.mk_Iio_lt x hord).trans_le hX

/-- The complete `m = 1` finite-support coding lemma.  The selected point of a nonempty finite
set is its maximum in a CH well-order; its predecessor set is countable, so the rest of the set
has a local natural code. -/
private theorem exists_supportFingerprint_of_mk_le_aleph_one {X : Type*}
    (ambient : X → ℝ) (hX : Cardinal.mk X ≤ Cardinal.aleph 1) :
    ∃ select : (s : Finset X) → s.Nonempty → X,
      ∃ G : Finset X → SupportFingerprint,
        (∀ (s : Finset X) (hs : s.Nonempty), select s hs ∈ s) ∧
        ∀ (s t : Finset X) (hs : s.Nonempty) (ht : t.Nonempty),
          G s = G t →
            s.card = t.card ∧
            supportPosition ambient (select s hs) s =
              supportPosition ambient (select t ht) t ∧
            (select s hs = select t ht → s = t) := by
  obtain ⟨lo, wf, hcount⟩ := exists_wellOrder_countable_Iio hX
  let : LinearOrder X := lo
  let : WellFoundedLT X := wf
  have hcountIic : ∀ p : X, Countable (Set.Iic p) := by
    intro p
    rw [← Set.Iio_insert]
    exact (hcount p).insert p
  let select : (s : Finset X) → s.Nonempty → X := fun s hs ↦ s.max' hs
  let G : Finset X → SupportFingerprint := supportFingerprint hcountIic ambient
  refine ⟨select, G, ?_, ?_⟩
  · intro s hs
    exact Finset.max'_mem s hs
  · intro s t hs ht hG
    exact supportFingerprint_eq_imp hs ht hG

private theorem exists_realTranscendenceSupportFingerprint
    (hCH : ContinuumHypothesis) :
    ∃ select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
        RealTranscendenceBasisIndex,
      ∃ G : Finset RealTranscendenceBasisIndex → SupportFingerprint,
        (∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
          select s hs ∈ s) ∧
        ∀ (s t : Finset RealTranscendenceBasisIndex)
            (hs : s.Nonempty) (ht : t.Nonempty),
          G s = G t →
            s.card = t.card ∧
            supportPosition realTranscendenceBasisValue (select s hs) s =
              supportPosition realTranscendenceBasisValue (select t ht) t ∧
            (select s hs = select t ht → s = t) := by
  apply exists_supportFingerprint_of_mk_le_aleph_one realTranscendenceBasisValue
  exact (Cardinal.mk_subtype_le realTranscendenceBasisSet).trans_eq
    (Cardinal.mk_real.trans hCH)

/-! ### The countable chart/support color

The input box recorded in a canonical chart lies inside the chamber of strictly increasing
tuples.  Consequently a basis element shared by two points carrying the same chart can occur
in only one chart coordinate.  The selected support element is recorded by that coordinate.
-/

private noncomputable def selectedChartCoordinate
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : (pointTranscendenceSupport x).Nonempty) :
    Fin (pointAlgebraicChartCode x).1 :=
  Fin.cast (pointChartCardEq x).symm
    (((pointTranscendenceSupport x).orderIsoOfFin rfl).symm
      ⟨select (pointTranscendenceSupport x) hx,
        hselect (pointTranscendenceSupport x) hx⟩)

private theorem pointChartSupportIndex_selected
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (hx : (pointTranscendenceSupport x).Nonempty) :
    pointChartSupportIndex x (selectedChartCoordinate select hselect x hx) =
      select (pointTranscendenceSupport x) hx := by
  change
    (((pointTranscendenceSupport x).orderIsoOfFin rfl)
      (((pointTranscendenceSupport x).orderIsoOfFin rfl).symm
        ⟨select (pointTranscendenceSupport x) hx,
          hselect (pointTranscendenceSupport x) hx⟩)).1 =
      select (pointTranscendenceSupport x) hx
  rw [OrderIso.apply_symm_apply]

private abbrev MasterColorCode :=
  Sum ℕ (ℕ × SupportFingerprint × ℕ)

private noncomputable def masterColorData
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : MasterColorCode :=
  if hx : (pointTranscendenceSupport x).Nonempty then
    Sum.inr
      (algebraicChartCodeEmbedding n (pointAlgebraicChartCode x),
        G (pointTranscendenceSupport x),
        (selectedChartCoordinate select hselect x hx).val)
  else
    Sum.inl (emptySupportPointCode n ⟨x, Finset.not_nonempty_iff_eq_empty.mp hx⟩)

private noncomputable def masterColor
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℕ :=
  Encodable.encode (masterColorData select hselect G x)

private theorem masterColorData_eq_of_color_eq
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : masterColor select hselect G x = masterColor select hselect G y) :
    masterColorData select hselect G x = masterColorData select hselect G y := by
  exact Encodable.encode_injective hxy

private theorem point_eq_of_chart_and_support_eq {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hchart : pointAlgebraicChartCode x = pointAlgebraicChartCode y)
    (hsupport : pointTranscendenceSupport x = pointTranscendenceSupport y) :
    x = y := by
  let Package := Σ c : AlgebraicChartCode n, Fin c.1 → ℝ
  let px : Package := ⟨pointAlgebraicChartCode x, pointChartParameters x⟩
  let py : Package := ⟨pointAlgebraicChartCode y, pointChartParameters y⟩
  have hk : (pointAlgebraicChartCode x).1 =
      (pointAlgebraicChartCode y).1 := congrArg Sigma.fst hchart
  let gy : Fin (pointAlgebraicChartCode x).1 → ℝ :=
    fun j ↦ pointChartParameters y (Fin.cast hk j)
  have hgy : StrictMono gy :=
    (pointChartParameters_strictMono y).comp
      (Fin.castOrderIso hk).strictMono
  have hgyRange : Set.range gy = Set.range (pointChartParameters y) := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.cast hk j, rfl⟩
    · rintro ⟨j, rfl⟩
      refine ⟨Fin.cast hk.symm j, ?_⟩
      simp [gy]
  have hrange : Set.range (pointChartParameters x) = Set.range gy := by
    rw [hgyRange, pointChartParameters_range, pointChartParameters_range,
      hsupport]
  have hfun : pointChartParameters x = gy :=
    (pointChartParameters_strictMono x).range_inj hgy |>.mp hrange
  have hparam : HEq (pointChartParameters x) (pointChartParameters y) := by
    apply (Fin.heq_fun_iff hk).2
    intro j
    exact congrFun hfun j
  have hpkg : px = py := Sigma.ext hchart hparam
  have hx : chartPoint px.1 px.2 = x := by
    apply WithLp.ofLp_injective 2
    funext i
    exact pointChartParameters_value x i
  have hy : chartPoint py.1 py.2 = y := by
    apply WithLp.ofLp_injective 2
    funext i
    exact pointChartParameters_value y i
  exact hx.symm.trans ((congrArg (fun p : Package ↦ chartPoint p.1 p.2) hpkg).trans hy)

private theorem support_nonempty_of_masterColor_eq_of_ne
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : masterColor select hselect G x = masterColor select hselect G y)
    (hne : x ≠ y) :
    (pointTranscendenceSupport x).Nonempty ∧
      (pointTranscendenceSupport y).Nonempty := by
  have hdata := masterColorData_eq_of_color_eq select hselect G hxy
  by_cases hx : (pointTranscendenceSupport x).Nonempty
  · by_cases hy : (pointTranscendenceSupport y).Nonempty
    · exact ⟨hx, hy⟩
    · simp [masterColorData, hx, hy] at hdata
  · by_cases hy : (pointTranscendenceSupport y).Nonempty
    · simp [masterColorData, hx, hy] at hdata
    · have hcode :
          emptySupportPointCode n
              ⟨x, Finset.not_nonempty_iff_eq_empty.mp hx⟩ =
            emptySupportPointCode n
              ⟨y, Finset.not_nonempty_iff_eq_empty.mp hy⟩ := by
        simpa [masterColorData, hx, hy] using hdata
      have hsub := (emptySupportPointCode n).injective hcode
      exact (hne (congrArg Subtype.val hsub)).elim

private theorem masterColor_nonempty_info
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)}
    (hx : (pointTranscendenceSupport x).Nonempty)
    (hy : (pointTranscendenceSupport y).Nonempty)
    (hxy : masterColor select hselect G x = masterColor select hselect G y) :
    pointAlgebraicChartCode x = pointAlgebraicChartCode y ∧
      G (pointTranscendenceSupport x) = G (pointTranscendenceSupport y) ∧
      (selectedChartCoordinate select hselect x hx).val =
        (selectedChartCoordinate select hselect y hy).val := by
  have hdata := masterColorData_eq_of_color_eq select hselect G hxy
  have htuple :
      (algebraicChartCodeEmbedding n (pointAlgebraicChartCode x),
          G (pointTranscendenceSupport x),
          (selectedChartCoordinate select hselect x hx).val) =
        (algebraicChartCodeEmbedding n (pointAlgebraicChartCode y),
          G (pointTranscendenceSupport y),
          (selectedChartCoordinate select hselect y hy).val) := by
    simpa [masterColorData, hx, hy] using hdata
  refine ⟨(algebraicChartCodeEmbedding n).injective
      (congrArg (fun z ↦ z.1) htuple), ?_, ?_⟩
  · exact congrArg (fun z ↦ z.2.1) htuple
  · exact congrArg (fun z ↦ z.2.2) htuple

private def chartInputIntervalNat {n : ℕ} (c : AlgebraicChartCode n)
    (r : ℕ) : ℚ × ℚ :=
  if hr : r < c.1 then c.2.2.1 ⟨r, hr⟩ else (0, 0)

private theorem shared_support_index_same_coordinate {n : ℕ}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hchart : pointAlgebraicChartCode x = pointAlgebraicChartCode y)
    {r s : ℕ} (hr : r < (pointAlgebraicChartCode x).1)
    (hs : s < (pointAlgebraicChartCode y).1)
    (hindex :
      pointChartSupportIndex x ⟨r, hr⟩ = pointChartSupportIndex y ⟨s, hs⟩) :
    r = s := by
  let ix : Fin (pointAlgebraicChartCode x).1 := ⟨r, hr⟩
  let jy : Fin (pointAlgebraicChartCode y).1 := ⟨s, hs⟩
  have hk : (pointAlgebraicChartCode x).1 =
      (pointAlgebraicChartCode y).1 := congrArg Sigma.fst hchart
  have hsx : s < (pointAlgebraicChartCode x).1 := hk ▸ hs
  let jx : Fin (pointAlgebraicChartCode x).1 := ⟨s, hsx⟩
  have hvalue : pointChartParameters x ix = pointChartParameters y jy := by
    rw [pointChartParameters_eq_basisValue, pointChartParameters_eq_basisValue,
      hindex]
  have hinterval :
      (pointAlgebraicChartCode x).2.2.1 jx =
        (pointAlgebraicChartCode y).2.2.1 jy := by
    have hh := congrArg (fun c ↦ chartInputIntervalNat c s) hchart
    simpa [chartInputIntervalNat, jx, jy, hsx, hs] using hh
  have hyIn : inRationalInterval
      ((pointAlgebraicChartCode x).2.2.1 jx) (pointChartParameters y jy) := by
    rw [hinterval]
    exact pointChartParameters_input y jy
  rcases lt_trichotomy r s with hrs | hrs | hsr
  · let v := Function.update (pointChartParameters x) jx (pointChartParameters y jy)
    have hvbox : chartInputBox (pointAlgebraicChartCode x) v := by
      intro l
      by_cases hlj : l = jx
      · subst l
        simpa [v, Function.update] using hyIn
      · simpa [v, Function.update, hlj] using pointChartParameters_input x l
    have hvstrict := (pointAlgebraicChartCode_spec x).choose_spec.2.1 v hvbox
    have hij : ix < jx := hrs
    have hlt := hvstrict hij
    have hne : ix ≠ jx := ne_of_lt hij
    simp [v, Function.update, hne] at hlt
    exact ((ne_of_lt hlt) hvalue).elim
  · exact hrs
  · let v := Function.update (pointChartParameters x) jx (pointChartParameters y jy)
    have hvbox : chartInputBox (pointAlgebraicChartCode x) v := by
      intro l
      by_cases hlj : l = jx
      · subst l
        simpa [v, Function.update] using hyIn
      · simpa [v, Function.update, hlj] using pointChartParameters_input x l
    have hvstrict := (pointAlgebraicChartCode_spec x).choose_spec.2.1 v hvbox
    have hji : jx < ix := hsr
    have hlt := hvstrict hji
    have hne : ix ≠ jx := ne_of_gt hji
    simp [v, Function.update, hne] at hlt
    exact ((ne_of_lt hlt) hvalue.symm).elim

private lemma chartInputBox_update {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin c.1 → ℝ) (j : Fin c.1) {z : ℝ}
    (hu : chartInputBox c u) (hz : inRationalInterval (c.2.2.1 j) z) :
    chartInputBox c (Function.update u j z) := by
  intro l
  by_cases hlj : l = j
  · subst l
    simpa [Function.update] using hz
  · simpa [Function.update, hlj] using hu l

private theorem analyticOnNhd_chartValue_update {n : ℕ}
    (c : AlgebraicChartCode n) (u : Fin c.1 → ℝ)
    (i : Fin n) (j : Fin c.1)
    (hu : chartInputBox c u)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0) :
    AnalyticOnNhd ℝ (fun z ↦ chartValue c (Function.update u j z) i)
      (Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ)) := by
  intro z hz
  have hzbox := chartInputBox_update c u j hu hz
  let v := Function.update u j z
  have han := isAlgebraicAnalyticAtOver_chartValue_update (K := ℝ) c v i j v
    (fun l hlj ↦ rfl) hzbox hunique (hderiv v hzbox i)
  have hvj : v j = z := by simp [v, Function.update]
  rw [← hvj]
  apply han.1.congr
  exact Filter.Eventually.of_forall fun w ↦ by
    change chartValue c (Function.update v j w) i =
      chartValue c (Function.update u j w) i
    apply congrArg (fun q ↦ chartValue c q i)
    funext l
    by_cases hlj : l = j
    · subst l
      simp
    · simp [v, Function.update, hlj]

private theorem IsAlgebraicAnalyticAtOver.sum_fin
    {K : Type*} [Field K] [Algebra K ℝ]
    {m : ℕ} {f : Fin m → ℝ → ℝ} {t : ℝ}
    (hf : ∀ i, IsAlgebraicAnalyticAtOver K (f i) t) :
    IsAlgebraicAnalyticAtOver K (fun z ↦ ∑ i, f i z) t := by
  classical
  have hsum : ∀ s : Finset (Fin m),
      IsAlgebraicAnalyticAtOver K (fun z ↦ ∑ i ∈ s, f i z) t := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (isAlgebraicAnalyticAtOver_const
          (K := K) (y := (0 : ℝ)) (t := t) isAlgebraic_zero)
    | insert a s ha ih =>
        rw [show (fun z ↦ ∑ i ∈ insert a s, f i z) =
            (fun z ↦ f a z + ∑ i ∈ s, f i z) by
          funext z
          simp [ha]]
        exact (hf a).add ih
  simpa using hsum Finset.univ

private theorem isAlgebraicAnalyticAtOver_squaredDistance
    {K : Type*} [Field K] [Algebra K ℝ]
    {n : ℕ} {f g : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ i, IsAlgebraicAnalyticAtOver K (fun z ↦ f z i) t)
    (hg : ∀ i, IsAlgebraicAnalyticAtOver K (fun z ↦ g z i) t) :
    IsAlgebraicAnalyticAtOver K (fun z ↦ squaredDistance (f z) (g z)) t := by
  apply IsAlgebraicAnalyticAtOver.sum_fin
  intro i
  exact (hf i).sub (hg i) |>.pow 2

private theorem isAlgebraicAnalyticAtOver_distancePolynomial3
    {K : Type*} [Field K] [Algebra K ℝ]
    {n : ℕ} {f : Fin 3 → ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ r i, IsAlgebraicAnalyticAtOver K (fun z ↦ f r z i) t) :
    IsAlgebraicAnalyticAtOver K
      (fun z ↦ distancePolynomial3 (f 0 z) (f 1 z) (f 2 z)) t := by
  exact (isAlgebraicAnalyticAtOver_squaredDistance (hf 0) (hf 1)).sub
    (isAlgebraicAnalyticAtOver_squaredDistance (hf 0) (hf 2))

private theorem isAlgebraicAnalyticAtOver_distancePolynomial4
    {K : Type*} [Field K] [Algebra K ℝ]
    {n : ℕ} {f : Fin 4 → ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hf : ∀ r i, IsAlgebraicAnalyticAtOver K (fun z ↦ f r z i) t) :
    IsAlgebraicAnalyticAtOver K
      (fun z ↦ distancePolynomial4 (f 0 z) (f 1 z) (f 2 z) (f 3 z)) t := by
  exact (isAlgebraicAnalyticAtOver_squaredDistance (hf 0) (hf 1)).sub
    (isAlgebraicAnalyticAtOver_squaredDistance (hf 2) (hf 3))

private theorem analyticAt_sum_fin {m : ℕ} {f : Fin m → ℝ → ℝ} {t : ℝ}
    (hf : ∀ i, AnalyticAt ℝ (f i) t) :
    AnalyticAt ℝ (fun z ↦ ∑ i, f i z) t := by
  classical
  have h := Finset.univ.analyticAt_sum (fun i _ ↦ hf i)
  apply h.congr
  exact Filter.Eventually.of_forall fun z ↦ by simp

private theorem analyticOnNhd_squaredDistance
    {n : ℕ} {f g : ℝ → EuclideanSpace ℝ (Fin n)} {U : Set ℝ}
    (hf : ∀ i, AnalyticOnNhd ℝ (fun z ↦ f z i) U)
    (hg : ∀ i, AnalyticOnNhd ℝ (fun z ↦ g z i) U) :
    AnalyticOnNhd ℝ (fun z ↦ squaredDistance (f z) (g z)) U := by
  intro z hz
  apply analyticAt_sum_fin
  intro i
  exact ((hf i z hz).sub (hg i z hz)).pow 2

private theorem analyticOnNhd_distancePolynomial3
    {n : ℕ} {f : Fin 3 → ℝ → EuclideanSpace ℝ (Fin n)} {U : Set ℝ}
    (hf : ∀ r i, AnalyticOnNhd ℝ (fun z ↦ f r z i) U) :
    AnalyticOnNhd ℝ
      (fun z ↦ distancePolynomial3 (f 0 z) (f 1 z) (f 2 z)) U :=
  (analyticOnNhd_squaredDistance (hf 0) (hf 1)).sub
    (analyticOnNhd_squaredDistance (hf 0) (hf 2))

private theorem analyticOnNhd_distancePolynomial4
    {n : ℕ} {f : Fin 4 → ℝ → EuclideanSpace ℝ (Fin n)} {U : Set ℝ}
    (hf : ∀ r i, AnalyticOnNhd ℝ (fun z ↦ f r z i) U) :
    AnalyticOnNhd ℝ
      (fun z ↦ distancePolynomial4 (f 0 z) (f 1 z) (f 2 z) (f 3 z)) U :=
  (analyticOnNhd_squaredDistance (hf 0) (hf 1)).sub
    (analyticOnNhd_squaredDistance (hf 2) (hf 3))

private noncomputable def replaceBasisParameter {m n : ℕ} {c : AlgebraicChartCode n}
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t : RealTranscendenceBasisIndex) (z : ℝ)
    (r : Fin m) (l : Fin c.1) : ℝ :=
  if idx r l = t then z else u r l

private theorem replaceBasisParameter_eq_update
    {m n : ℕ} {c : AlgebraicChartCode n}
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t : RealTranscendenceBasisIndex) (j : Fin c.1)
    (hposition : ∀ r s l q, idx r l = idx s q → l = q)
    {r : Fin m} (hrj : idx r j = t) (z : ℝ) :
    (fun l ↦ replaceBasisParameter u idx t z r l) =
      Function.update (u r) j z := by
  funext q
  by_cases hq : idx r q = t
  · have hqj : q = j := hposition r r q j (hq.trans hrj.symm)
    subst q
    simp [replaceBasisParameter, hrj, Function.update]
  · have hqj : q ≠ j := by
      intro h
      subst q
      exact hq hrj
    simp [replaceBasisParameter, hq, Function.update, hqj]

private theorem replaceBasisParameter_eq_self
    {m n : ℕ} {c : AlgebraicChartCode n}
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t : RealTranscendenceBasisIndex) {r : Fin m}
    (hr : ¬ ∃ l, idx r l = t) (z : ℝ) :
    (fun l ↦ replaceBasisParameter u idx t z r l) = u r := by
  funext l
  have hne : idx r l ≠ t := fun h ↦ hr ⟨l, h⟩
  simp [replaceBasisParameter, hne]

private theorem replaceBasisParameter_at_basisValue
    {m n : ℕ} {c : AlgebraicChartCode n}
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hu : ∀ r l, u r l = realTranscendenceBasisValue (idx r l))
    (t : RealTranscendenceBasisIndex) (r : Fin m) :
    (fun l ↦ replaceBasisParameter u idx t
      (realTranscendenceBasisValue t) r l) = u r := by
  funext l
  by_cases hlt : idx r l = t
  · simp [replaceBasisParameter, hlt, hu]
  · simp [replaceBasisParameter, hlt]

private noncomputable def substitutionPoint
    {m n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t : RealTranscendenceBasisIndex) (r : Fin m) (z : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  chartPoint c (fun l ↦ replaceBasisParameter u idx t z r l)

private theorem substitutionPoint_at_basisValue
    {m n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hu : ∀ r l, u r l = realTranscendenceBasisValue (idx r l))
    (t : RealTranscendenceBasisIndex) (r : Fin m) :
    substitutionPoint c u idx t r (realTranscendenceBasisValue t) =
      chartPoint c (u r) := by
  rw [substitutionPoint, replaceBasisParameter_at_basisValue u idx hu]

private theorem substitutionPoint_coordinate_isAlgebraicAnalyticAt
    {m n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hu : ∀ r l, u r l = realTranscendenceBasisValue (idx r l))
    (hposition : ∀ r s l q, idx r l = idx s q → l = q)
    (hbox : ∀ r, chartInputBox c (u r))
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (a : Fin m) (j : Fin c.1)
    (r : Fin m) (i : Fin n) :
    IsAlgebraicAnalyticAtOver (PivotBaseField (idx a j))
      (fun z ↦ substitutionPoint c u idx (idx a j) r z i)
      (realTranscendenceBasisValue (idx a j)) := by
  let t := idx a j
  by_cases hr : ∃ l, idx r l = t
  · obtain ⟨l, hl⟩ := hr
    have hlj : l = j := hposition r a l j hl
    subst l
    let fixed : Fin c.1 → PivotBaseField t := fun q ↦
      if hqj : q = j then 0
      else basisValueInPivotBaseField t (idx r q) (by
        intro heq
        exact hqj (hposition r a q j heq))
    have hfixed : ∀ q, q ≠ j →
        algebraMap (PivotBaseField t) ℝ (fixed q) = u r q := by
      intro q hqj
      rw [show fixed q = basisValueInPivotBaseField t (idx r q) (by
          intro heq
          exact hqj (hposition r a q j heq)) by simp [fixed, hqj],
        algebraMap_basisValueInPivotBaseField, hu]
    have halg := isAlgebraicAnalyticAtOver_chartValue_update c (u r) i j fixed
      hfixed (hbox r) hunique (hderiv (u r) (hbox r) i)
    have hcenter : u r j = realTranscendenceBasisValue t := by
      rw [hu, hl]
    rw [hcenter] at halg
    apply halg.congr
    exact Filter.Eventually.of_forall fun z ↦ by
      change chartValue c (Function.update (u r) j z) i =
        chartValue c (fun l ↦ replaceBasisParameter u idx t z r l) i
      rw [replaceBasisParameter_eq_update u idx t j hposition hl z]
  · let fixed : Fin c.1 → PivotBaseField t := fun q ↦
      basisValueInPivotBaseField t (idx r q) (fun heq ↦ hr ⟨q, heq⟩)
    have hfixed : ∀ q,
        algebraMap (PivotBaseField t) ℝ (fixed q) = u r q := by
      intro q
      rw [show fixed q = basisValueInPivotBaseField t (idx r q)
          (fun heq ↦ hr ⟨q, heq⟩) by rfl,
        algebraMap_basisValueInPivotBaseField, hu]
    have halgebraic := chartValue_isAlgebraic_of_parameters c (u r) i fixed
      hfixed (hbox r) hunique (hderiv (u r) (hbox r) i)
    have hconst := isAlgebraicAnalyticAtOver_const
      (K := PivotBaseField t) (t := realTranscendenceBasisValue t) halgebraic
    apply hconst.congr
    exact Filter.Eventually.of_forall fun z ↦ by
      change chartValue c (u r) i =
        chartValue c (fun l ↦ replaceBasisParameter u idx t z r l) i
      rw [replaceBasisParameter_eq_self u idx t hr z]

private theorem substitutionPoint_coordinate_analyticOn
    {m n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin m → Fin c.1 → ℝ)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hposition : ∀ r s l q, idx r l = idx s q → l = q)
    (hbox : ∀ r, chartInputBox c (u r))
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (a : Fin m) (j : Fin c.1) (r : Fin m) (i : Fin n) :
    AnalyticOnNhd ℝ
      (fun z ↦ substitutionPoint c u idx (idx a j) r z i)
      (Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ)) := by
  let t := idx a j
  by_cases hr : ∃ l, idx r l = t
  · obtain ⟨l, hl⟩ := hr
    have hlj : l = j := hposition r a l j hl
    subst l
    have han := analyticOnNhd_chartValue_update c (u r) i j (hbox r) hunique hderiv
    apply AnalyticOnNhd.congr isOpen_Ioo han
    intro z hz
    change chartValue c (Function.update (u r) j z) i =
      chartValue c (fun l ↦ replaceBasisParameter u idx t z r l) i
    rw [replaceBasisParameter_eq_update u idx t j hposition hl z]
  · have han : AnalyticOnNhd ℝ (fun _ : ℝ ↦ chartValue c (u r) i)
      (Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ)) :=
      fun _ _ ↦ analyticAt_const
    apply AnalyticOnNhd.congr isOpen_Ioo han
    intro z hz
    change chartValue c (u r) i =
      chartValue c (fun l ↦ replaceBasisParameter u idx t z r l) i
    rw [replaceBasisParameter_eq_self u idx t hr z]

private theorem distancePolynomial3_zero_after_one_substitution
    {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin 3 → Fin c.1 → ℝ)
    (idx : Fin 3 → Fin c.1 → RealTranscendenceBasisIndex)
    (hu : ∀ r l, u r l = realTranscendenceBasisValue (idx r l))
    (hposition : ∀ r s l q, idx r l = idx s q → l = q)
    (hbox : ∀ r, chartInputBox c (u r))
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (a : Fin 3) (j : Fin c.1)
    (hzero : distancePolynomial3 (chartPoint c (u 0))
      (chartPoint c (u 1)) (chartPoint c (u 2)) = 0)
    {z : ℝ} (hz : inRationalInterval (c.2.2.1 j) z) :
    distancePolynomial3
      (substitutionPoint c u idx (idx a j) 0 z)
      (substitutionPoint c u idx (idx a j) 1 z)
      (substitutionPoint c u idx (idx a j) 2 z) = 0 := by
  let f : Fin 3 → ℝ → EuclideanSpace ℝ (Fin n) :=
    fun r z ↦ substitutionPoint c u idx (idx a j) r z
  have halg : IsAlgebraicAnalyticAtOver (PivotBaseField (idx a j))
      (fun z ↦ distancePolynomial3 (f 0 z) (f 1 z) (f 2 z))
      (realTranscendenceBasisValue (idx a j)) :=
    isAlgebraicAnalyticAtOver_distancePolynomial3 fun r i ↦
      substitutionPoint_coordinate_isAlgebraicAnalyticAt c u idx hu hposition
        hbox hunique hderiv a j r i
  have hcenter :
      distancePolynomial3
          (f 0 (realTranscendenceBasisValue (idx a j)))
          (f 1 (realTranscendenceBasisValue (idx a j)))
          (f 2 (realTranscendenceBasisValue (idx a j))) = 0 := by
    simp only [f, substitutionPoint_at_basisValue c u idx hu]
    exact hzero
  have hlocal := algebraicAnalytic_zero_at_transcendental_over
    (pivot_transcendental (idx a j)) halg hcenter
  let U := Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ)
  have han : AnalyticOnNhd ℝ
      (fun z ↦ distancePolynomial3 (f 0 z) (f 1 z) (f 2 z)) U :=
    analyticOnNhd_distancePolynomial3 fun r i ↦
      substitutionPoint_coordinate_analyticOn c u idx hposition hbox hunique hderiv
        a j r i
  have hcenterU : realTranscendenceBasisValue (idx a j) ∈ U := by
    change inRationalInterval (c.2.2.1 j)
      (realTranscendenceBasisValue (idx a j))
    rw [← hu a j]
    exact hbox a j
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioo hcenterU hlocal hz

private theorem distancePolynomial4_zero_after_one_substitution
    {n : ℕ} (c : AlgebraicChartCode n)
    (u : Fin 4 → Fin c.1 → ℝ)
    (idx : Fin 4 → Fin c.1 → RealTranscendenceBasisIndex)
    (hu : ∀ r l, u r l = realTranscendenceBasisValue (idx r l))
    (hposition : ∀ r s l q, idx r l = idx s q → l = q)
    (hbox : ∀ r, chartInputBox c (u r))
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (a : Fin 4) (j : Fin c.1)
    (hzero : distancePolynomial4 (chartPoint c (u 0))
      (chartPoint c (u 1)) (chartPoint c (u 2)) (chartPoint c (u 3)) = 0)
    {z : ℝ} (hz : inRationalInterval (c.2.2.1 j) z) :
    distancePolynomial4
      (substitutionPoint c u idx (idx a j) 0 z)
      (substitutionPoint c u idx (idx a j) 1 z)
      (substitutionPoint c u idx (idx a j) 2 z)
      (substitutionPoint c u idx (idx a j) 3 z) = 0 := by
  let f : Fin 4 → ℝ → EuclideanSpace ℝ (Fin n) :=
    fun r z ↦ substitutionPoint c u idx (idx a j) r z
  have halg : IsAlgebraicAnalyticAtOver (PivotBaseField (idx a j))
      (fun z ↦ distancePolynomial4 (f 0 z) (f 1 z) (f 2 z) (f 3 z))
      (realTranscendenceBasisValue (idx a j)) :=
    isAlgebraicAnalyticAtOver_distancePolynomial4 fun r i ↦
      substitutionPoint_coordinate_isAlgebraicAnalyticAt c u idx hu hposition
        hbox hunique hderiv a j r i
  have hcenter :
      distancePolynomial4
          (f 0 (realTranscendenceBasisValue (idx a j)))
          (f 1 (realTranscendenceBasisValue (idx a j)))
          (f 2 (realTranscendenceBasisValue (idx a j)))
          (f 3 (realTranscendenceBasisValue (idx a j))) = 0 := by
    simp only [f, substitutionPoint_at_basisValue c u idx hu]
    exact hzero
  have hlocal := algebraicAnalytic_zero_at_transcendental_over
    (pivot_transcendental (idx a j)) halg hcenter
  let U := Set.Ioo ((c.2.2.1 j).1 : ℝ) ((c.2.2.1 j).2 : ℝ)
  have han : AnalyticOnNhd ℝ
      (fun z ↦ distancePolynomial4 (f 0 z) (f 1 z) (f 2 z) (f 3 z)) U :=
    analyticOnNhd_distancePolynomial4 fun r i ↦
      substitutionPoint_coordinate_analyticOn c u idx hposition hbox hunique hderiv
        a j r i
  have hcenterU : realTranscendenceBasisValue (idx a j) ∈ U := by
    change inRationalInterval (c.2.2.1 j)
      (realTranscendenceBasisValue (idx a j))
    rw [← hu a j]
    exact hbox a j
  exact han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioo hcenterU hlocal hz

private noncomputable def basisParameterMatrix
    {m n : ℕ} {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex) :
    Fin m → Fin c.1 → ℝ :=
  fun r l ↦ realTranscendenceBasisValue (idx r l)

private noncomputable def replaceBasisIndex
    {m n : ℕ} {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t s : RealTranscendenceBasisIndex) :
    Fin m → Fin c.1 → RealTranscendenceBasisIndex :=
  fun r l ↦ if idx r l = t then s else idx r l

private theorem replaceParameterMatrix_eq
    {m n : ℕ} {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (t s : RealTranscendenceBasisIndex) (r : Fin m) :
    (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx t
      (realTranscendenceBasisValue s) r l) =
      basisParameterMatrix (replaceBasisIndex idx t s) r := by
  funext l
  by_cases h : idx r l = t <;>
    simp [replaceBasisParameter, replaceBasisIndex, basisParameterMatrix, h]

private def IndexPositionConsistent
    {m n : ℕ} {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex) : Prop :=
  ∀ r s l q, idx r l = idx s q → l = q

private def IndexMatrixInBox
    {m n : ℕ} (c : AlgebraicChartCode n)
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex) : Prop :=
  ∀ r, chartInputBox c (basisParameterMatrix idx r)

private theorem replaceBasisIndex_position
    {m n : ℕ} {c : AlgebraicChartCode n}
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx)
    (a b : Fin m) (j : Fin c.1) :
    IndexPositionConsistent
      (replaceBasisIndex idx (idx a j) (idx b j)) := by
  intro r s l q heq
  by_cases hrl : idx r l = idx a j
  · by_cases hsq : idx s q = idx a j
    · exact (hpos r a l j hrl).trans (hpos s a q j hsq).symm
    · simp [replaceBasisIndex, hrl, hsq] at heq
      exact (hpos r a l j hrl).trans (hpos b s j q heq)
  · by_cases hsq : idx s q = idx a j
    · simp [replaceBasisIndex, hrl, hsq] at heq
      exact (hpos r b l j heq).trans (hpos s a q j hsq).symm
    · simp [replaceBasisIndex, hrl, hsq] at heq
      exact hpos r s l q heq

private theorem replaceBasisIndex_box
    {m n : ℕ} {c : AlgebraicChartCode n}
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (a b : Fin m) (j : Fin c.1) :
    IndexMatrixInBox c (replaceBasisIndex idx (idx a j) (idx b j)) := by
  intro r l
  by_cases hrl : idx r l = idx a j
  · have hlj : l = j := hpos r a l j hrl
    subst l
    simpa [basisParameterMatrix, replaceBasisIndex, hrl] using hbox b j
  · simpa [basisParameterMatrix, replaceBasisIndex, hrl] using hbox r l

private noncomputable def indexNormalizationStep
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (p : Fin m × Fin c.1) :
    Fin m → Fin c.1 → RealTranscendenceBasisIndex :=
  replaceBasisIndex idx (idx p.1 p.2) (idx 0 p.2)

private noncomputable def normalizeIndices
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex) :
    Fin m → Fin c.1 → RealTranscendenceBasisIndex :=
  L.foldl indexNormalizationStep idx

private theorem indexNormalizationStep_position
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx) (p : Fin m × Fin c.1) :
    IndexPositionConsistent (indexNormalizationStep idx p) :=
  replaceBasisIndex_position hpos p.1 0 p.2

private theorem indexNormalizationStep_box
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (p : Fin m × Fin c.1) :
    IndexMatrixInBox c (indexNormalizationStep idx p) :=
  replaceBasisIndex_box hpos hbox p.1 0 p.2

private theorem normalizeIndices_position
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx) :
    IndexPositionConsistent (normalizeIndices L idx) := by
  induction L generalizing idx with
  | nil => exact hpos
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact ih (indexNormalizationStep_position hpos p)

private theorem normalizeIndices_box
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    {idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex}
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx) :
    IndexMatrixInBox c (normalizeIndices L idx) := by
  induction L generalizing idx with
  | nil => exact hbox
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact ih (indexNormalizationStep_position hpos p)
        (indexNormalizationStep_box hpos hbox p)

private theorem indexNormalizationStep_sets_equal
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (p : Fin m × Fin c.1) :
    indexNormalizationStep idx p p.1 p.2 =
      indexNormalizationStep idx p 0 p.2 := by
  simp only [indexNormalizationStep, replaceBasisIndex, if_pos]
  by_cases h : idx 0 p.2 = idx p.1 p.2
  · rw [if_pos h]
  · rw [if_neg h]

private theorem indexNormalizationStep_preserves_eq
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (p : Fin m × Fin c.1) {r s : Fin m} {j : Fin c.1}
    (h : idx r j = idx s j) :
    indexNormalizationStep idx p r j = indexNormalizationStep idx p s j := by
  simp only [indexNormalizationStep, replaceBasisIndex]
  by_cases hr : idx r j = idx p.1 p.2
  · have hs : idx s j = idx p.1 p.2 := h.symm.trans hr
    simp [hr, hs]
  · have hs : idx s j ≠ idx p.1 p.2 := fun hs ↦ hr (h.trans hs)
    simp [hr, hs, h]

private theorem normalizeIndices_preserves_eq
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    {r s : Fin m} {j : Fin c.1} (h : idx r j = idx s j) :
    normalizeIndices L idx r j = normalizeIndices L idx s j := by
  induction L generalizing idx with
  | nil => exact h
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact ih (indexNormalizationStep idx p)
        (indexNormalizationStep_preserves_eq idx p h)

private theorem normalizeIndices_eq_of_mem
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    {p : Fin m × Fin c.1} (hp : p ∈ L) :
    normalizeIndices L idx p.1 p.2 = normalizeIndices L idx 0 p.2 := by
  induction L generalizing idx with
  | nil => simp at hp
  | cons q L ih =>
      simp only [List.mem_cons] at hp
      rw [normalizeIndices, List.foldl_cons]
      rcases hp with rfl | hp
      · exact normalizeIndices_preserves_eq L (indexNormalizationStep idx p)
          (indexNormalizationStep_sets_equal idx p)
      · exact ih (idx := indexNormalizationStep idx q) hp

private theorem indexNormalizationStep_base
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx)
    (p : Fin m × Fin c.1) (j : Fin c.1) :
    indexNormalizationStep idx p 0 j = idx 0 j := by
  by_cases h : idx 0 j = idx p.1 p.2
  · have hj : j = p.2 := hpos 0 p.1 j p.2 h
    subst j
    simp [indexNormalizationStep, replaceBasisIndex]
  · simp [indexNormalizationStep, replaceBasisIndex, h]

private theorem normalizeIndices_base
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx)
    (j : Fin c.1) : normalizeIndices L idx 0 j = idx 0 j := by
  induction L generalizing idx with
  | nil => rfl
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact (ih (indexNormalizationStep idx p)
        (indexNormalizationStep_position hpos p)).trans
          (indexNormalizationStep_base idx hpos p j)

private theorem distancePolynomial3_zero_indexNormalizationStep
    {n : ℕ} (c : AlgebraicChartCode n)
    (idx : Fin 3 → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (p : Fin 3 × Fin c.1)
    (hzero : distancePolynomial3
      (chartPoint c (basisParameterMatrix idx 0))
      (chartPoint c (basisParameterMatrix idx 1))
      (chartPoint c (basisParameterMatrix idx 2)) = 0) :
    distancePolynomial3
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 0))
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 1))
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 2)) = 0 := by
  have h := distancePolynomial3_zero_after_one_substitution c
    (basisParameterMatrix idx) idx (fun _ _ ↦ rfl) hpos hbox hunique hderiv
    p.1 p.2 hzero (hbox 0 p.2)
  change distancePolynomial3
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 0 l))
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 1 l))
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 2 l)) = 0 at h
  simpa only [indexNormalizationStep,
    replaceParameterMatrix_eq idx (idx p.1 p.2) (idx 0 p.2)] using h

private theorem distancePolynomial4_zero_indexNormalizationStep
    {n : ℕ} (c : AlgebraicChartCode n)
    (idx : Fin 4 → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (p : Fin 4 × Fin c.1)
    (hzero : distancePolynomial4
      (chartPoint c (basisParameterMatrix idx 0))
      (chartPoint c (basisParameterMatrix idx 1))
      (chartPoint c (basisParameterMatrix idx 2))
      (chartPoint c (basisParameterMatrix idx 3)) = 0) :
    distancePolynomial4
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 0))
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 1))
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 2))
      (chartPoint c (basisParameterMatrix (indexNormalizationStep idx p) 3)) = 0 := by
  have h := distancePolynomial4_zero_after_one_substitution c
    (basisParameterMatrix idx) idx (fun _ _ ↦ rfl) hpos hbox hunique hderiv
    p.1 p.2 hzero (hbox 0 p.2)
  change distancePolynomial4
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 0 l))
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 1 l))
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 2 l))
      (chartPoint c (fun l ↦ replaceBasisParameter (basisParameterMatrix idx) idx
        (idx p.1 p.2) (realTranscendenceBasisValue (idx 0 p.2)) 3 l)) = 0 at h
  simpa only [indexNormalizationStep,
    replaceParameterMatrix_eq idx (idx p.1 p.2) (idx 0 p.2)] using h

private theorem distancePolynomial3_zero_normalizeIndices
    {n : ℕ} (c : AlgebraicChartCode n)
    (L : List (Fin 3 × Fin c.1))
    (idx : Fin 3 → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (hzero : distancePolynomial3
      (chartPoint c (basisParameterMatrix idx 0))
      (chartPoint c (basisParameterMatrix idx 1))
      (chartPoint c (basisParameterMatrix idx 2)) = 0) :
    distancePolynomial3
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 0))
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 1))
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 2)) = 0 := by
  induction L generalizing idx with
  | nil => exact hzero
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact ih (indexNormalizationStep idx p)
        (indexNormalizationStep_position hpos p)
        (indexNormalizationStep_box hpos hbox p)
        (distancePolynomial3_zero_indexNormalizationStep c idx hpos hbox hunique hderiv p hzero)

private theorem distancePolynomial4_zero_normalizeIndices
    {n : ℕ} (c : AlgebraicChartCode n)
    (L : List (Fin 4 × Fin c.1))
    (idx : Fin 4 → Fin c.1 → RealTranscendenceBasisIndex)
    (hpos : IndexPositionConsistent idx) (hbox : IndexMatrixInBox c idx)
    (hunique : ∀ v, chartInputBox c v → ∀ i, ∃! y, chartRoot c v i y)
    (hderiv : ∀ v, chartInputBox c v → ∀ i,
      evalChartPolynomial (c.2.1 i).derivative v (chartValue c v i) ≠ 0)
    (hzero : distancePolynomial4
      (chartPoint c (basisParameterMatrix idx 0))
      (chartPoint c (basisParameterMatrix idx 1))
      (chartPoint c (basisParameterMatrix idx 2))
      (chartPoint c (basisParameterMatrix idx 3)) = 0) :
    distancePolynomial4
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 0))
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 1))
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 2))
      (chartPoint c (basisParameterMatrix (normalizeIndices L idx) 3)) = 0 := by
  induction L generalizing idx with
  | nil => exact hzero
  | cons p L ih =>
      rw [normalizeIndices, List.foldl_cons]
      exact ih (indexNormalizationStep idx p)
        (indexNormalizationStep_position hpos p)
        (indexNormalizationStep_box hpos hbox p)
        (distancePolynomial4_zero_indexNormalizationStep c idx hpos hbox hunique hderiv p hzero)

private theorem normalizeIndices_preserves_unique_excluded
    {m n : ℕ} [NeZero m] {c : AlgebraicChartCode n}
    (L : List (Fin m × Fin c.1))
    (idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex)
    (q : Fin m × Fin c.1) (hq0 : q.1 ≠ 0)
    (hL : ∀ p ∈ L, p ≠ q)
    (hunique : ∀ p : Fin m × Fin c.1,
      idx p.1 p.2 = idx q.1 q.2 → p = q) :
    (normalizeIndices L idx q.1 q.2 = idx q.1 q.2) ∧
      ∀ p : Fin m × Fin c.1,
        normalizeIndices L idx p.1 p.2 = idx q.1 q.2 → p = q := by
  induction L generalizing idx with
  | nil => exact ⟨rfl, hunique⟩
  | cons p L ih =>
      have hpq : p ≠ q := hL p (by simp)
      have hsource : idx p.1 p.2 ≠ idx q.1 q.2 := by
        intro h
        exact hpq (hunique p h)
      have htarget : idx 0 p.2 ≠ idx q.1 q.2 := by
        intro h
        have heq : (0, p.2) = q := hunique (0, p.2) h
        exact hq0 (congrArg Prod.fst heq).symm
      have hstepQ : indexNormalizationStep idx p q.1 q.2 = idx q.1 q.2 := by
        have hqsource : idx q.1 q.2 ≠ idx p.1 p.2 := Ne.symm hsource
        simp [indexNormalizationStep, replaceBasisIndex, hqsource]
      have hstepUnique : ∀ r : Fin m × Fin c.1,
          indexNormalizationStep idx p r.1 r.2 = idx q.1 q.2 → r = q := by
        intro r hr
        by_cases hrs : idx r.1 r.2 = idx p.1 p.2
        · simp [indexNormalizationStep, replaceBasisIndex, hrs] at hr
          exact (htarget hr).elim
        · simp [indexNormalizationStep, replaceBasisIndex, hrs] at hr
          exact hunique r hr
      rw [normalizeIndices, List.foldl_cons]
      have htail := ih (indexNormalizationStep idx p)
        (fun r hr ↦ hL r (by simp [hr]))
        (by
          intro r hr
          have := hstepUnique r (hr.trans hstepQ)
          exact this)
      exact ⟨htail.1.trans hstepQ, fun r hr ↦ htail.2 r (hr.trans hstepQ.symm)⟩

private noncomputable def commonSupportIndex
    {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n))
    (hchart : pointAlgebraicChartCode x = c) :
    Fin c.1 → RealTranscendenceBasisIndex :=
  fun j ↦ pointChartSupportIndex x
    (Fin.cast (congrArg Sigma.fst hchart).symm j)

private theorem commonChartPackage_eq
    {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n))
    (hchart : pointAlgebraicChartCode x = c) :
    (⟨c, basisParameterMatrix (fun _ : Fin 1 ↦
        commonSupportIndex c x hchart) 0⟩ :
      Σ d : AlgebraicChartCode n, Fin d.1 → ℝ) =
      ⟨pointAlgebraicChartCode x, pointChartParameters x⟩ := by
  apply Sigma.ext hchart.symm
  have hk : c.1 = (pointAlgebraicChartCode x).1 :=
    congrArg Sigma.fst hchart.symm
  apply (Fin.heq_fun_iff hk).2
  intro j
  change realTranscendenceBasisValue
      (pointChartSupportIndex x (Fin.cast (congrArg Sigma.fst hchart).symm j)) =
    pointChartParameters x (Fin.cast hk j)
  rw [pointChartParameters_eq_basisValue]

private theorem chartPoint_commonSupportIndex
    {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n))
    (hchart : pointAlgebraicChartCode x = c) :
    chartPoint c (fun j ↦ realTranscendenceBasisValue
      (commonSupportIndex c x hchart j)) = x := by
  let Package := Σ d : AlgebraicChartCode n, Fin d.1 → ℝ
  have hpkg := commonChartPackage_eq c x hchart
  have hpoint := congrArg (fun p : Package ↦ chartPoint p.1 p.2) hpkg
  have hmatrix : basisParameterMatrix (fun _ : Fin 1 ↦
      commonSupportIndex c x hchart) 0 =
      (fun j ↦ realTranscendenceBasisValue
        (commonSupportIndex c x hchart j)) := rfl
  calc
    chartPoint c (fun j ↦ realTranscendenceBasisValue
        (commonSupportIndex c x hchart j)) =
        chartPoint (pointAlgebraicChartCode x) (pointChartParameters x) := by
          rw [← hmatrix]
          exact hpoint
    _ = x := by
      apply WithLp.ofLp_injective 2
      funext i
      exact pointChartParameters_value x i

private theorem commonSupportIndex_box
    {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n))
    (hchart : pointAlgebraicChartCode x = c) :
    chartInputBox c (fun j ↦ realTranscendenceBasisValue
      (commonSupportIndex c x hchart j)) := by
  let Package := Σ d : AlgebraicChartCode n, Fin d.1 → ℝ
  have hpkg := commonChartPackage_eq c x hchart
  have htransport := congrArg (fun p : Package ↦ chartInputBox p.1 p.2) hpkg
  have hx := pointChartParameters_input x
  change chartInputBox c (basisParameterMatrix
    (fun _ : Fin 1 ↦ commonSupportIndex c x hchart) 0)
  rw [htransport]
  exact hx

private theorem commonSupportIndex_position
    {n : ℕ} (c : AlgebraicChartCode n)
    {x y : EuclideanSpace ℝ (Fin n)}
    (hx : pointAlgebraicChartCode x = c)
    (hy : pointAlgebraicChartCode y = c)
    {i j : Fin c.1}
    (hindex : commonSupportIndex c x hx i = commonSupportIndex c y hy j) :
    i = j := by
  let ix : Fin (pointAlgebraicChartCode x).1 :=
    Fin.cast (congrArg Sigma.fst hx).symm i
  let jy : Fin (pointAlgebraicChartCode y).1 :=
    Fin.cast (congrArg Sigma.fst hy).symm j
  have hval := shared_support_index_same_coordinate (hx.trans hy.symm)
    ix.2 jy.2 hindex
  apply Fin.ext
  exact hval

private theorem commonSupportIndex_selected
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    {n : ℕ} (c : AlgebraicChartCode n)
    (x : EuclideanSpace ℝ (Fin n))
    (hx : (pointTranscendenceSupport x).Nonempty)
    (hchart : pointAlgebraicChartCode x = c)
    (j : Fin c.1)
    (hj : j.val = (selectedChartCoordinate select hselect x hx).val) :
    commonSupportIndex c x hchart j =
      select (pointTranscendenceSupport x) hx := by
  rw [← pointChartSupportIndex_selected select hselect x hx]
  apply congrArg (pointChartSupportIndex x)
  apply Fin.ext
  exact hj

private structure ChartConfiguration {m n : ℕ} [NeZero m]
    (x : Fin m → EuclideanSpace ℝ (Fin n)) where
  chart : AlgebraicChartCode n
  pivot : Fin chart.1
  index : Fin m → Fin chart.1 → RealTranscendenceBasisIndex
  position : IndexPositionConsistent index
  box : IndexMatrixInBox chart index
  realizes : ∀ r, chartPoint chart (basisParameterMatrix index r) = x r
  unique : ∀ v, chartInputBox chart v → ∀ i, ∃! y, chartRoot chart v i y
  derivative : ∀ v, chartInputBox chart v → ∀ i,
    evalChartPolynomial (chart.2.1 i).derivative v (chartValue chart v i) ≠ 0
  pivot_injective : Function.Injective (fun r ↦ index r pivot)
  curve_nonconstant : ∃ z,
    inRationalInterval (chart.2.2.1 pivot) z ∧
      chartPoint chart
        (Function.update (basisParameterMatrix index 0) pivot z) ≠ x 0

private theorem exists_chartConfiguration
    (select : (s : Finset RealTranscendenceBasisIndex) → s.Nonempty →
      RealTranscendenceBasisIndex)
    (G : Finset RealTranscendenceBasisIndex → SupportFingerprint)
    (hselect : ∀ (s : Finset RealTranscendenceBasisIndex) (hs : s.Nonempty),
      select s hs ∈ s)
    (hfp : ∀ (s t : Finset RealTranscendenceBasisIndex)
        (hs : s.Nonempty) (ht : t.Nonempty),
      G s = G t →
        s.card = t.card ∧
        supportPosition realTranscendenceBasisValue (select s hs) s =
          supportPosition realTranscendenceBasisValue (select t ht) t ∧
        (select s hs = select t ht → s = t))
    {m n : ℕ} [NeZero m]
    (x : Fin m → EuclideanSpace ℝ (Fin n))
    (hinj : Function.Injective x)
    (hother : ∀ r : Fin m, ∃ s : Fin m, s ≠ r)
    (hmono : ∀ r, masterColor select hselect G (x r) =
      masterColor select hselect G (x 0)) :
    Nonempty (ChartConfiguration x) := by
  have hsupp : ∀ r, (pointTranscendenceSupport (x r)).Nonempty := by
    intro r
    obtain ⟨s, hsr⟩ := hother r
    exact (support_nonempty_of_masterColor_eq_of_ne select hselect G
      ((hmono r).trans (hmono s).symm) (hinj.ne hsr.symm)).1
  let c := pointAlgebraicChartCode (x 0)
  have hinfo : ∀ r,
      pointAlgebraicChartCode (x r) = c ∧
        G (pointTranscendenceSupport (x r)) =
          G (pointTranscendenceSupport (x 0)) ∧
        (selectedChartCoordinate select hselect (x r) (hsupp r)).val =
          (selectedChartCoordinate select hselect (x 0) (hsupp 0)).val := by
    intro r
    exact masterColor_nonempty_info select hselect G (hsupp r) (hsupp 0) (hmono r)
  let j : Fin c.1 := selectedChartCoordinate select hselect (x 0) (hsupp 0)
  let idx : Fin m → Fin c.1 → RealTranscendenceBasisIndex := fun r ↦
    commonSupportIndex c (x r) (hinfo r).1
  have hpos : IndexPositionConsistent idx := by
    intro r s l q heq
    exact commonSupportIndex_position c (hinfo r).1 (hinfo s).1 heq
  have hbox : IndexMatrixInBox c idx := by
    intro r
    exact commonSupportIndex_box c (x r) (hinfo r).1
  have hrealizes : ∀ r, chartPoint c (basisParameterMatrix idx r) = x r := by
    intro r
    exact chartPoint_commonSupportIndex c (x r) (hinfo r).1
  have hpivot : ∀ r, idx r j =
      select (pointTranscendenceSupport (x r)) (hsupp r) := by
    intro r
    exact commonSupportIndex_selected select hselect c (x r) (hsupp r) (hinfo r).1 j
      (by
        change (selectedChartCoordinate select hselect (x 0) (hsupp 0)).val =
          (selectedChartCoordinate select hselect (x r) (hsupp r)).val
        exact (hinfo r).2.2.symm)
  have hpivotInj : Function.Injective (fun r ↦ idx r j) := by
    intro r s hrs
    apply hinj
    apply point_eq_of_chart_and_support_eq ((hinfo r).1.trans (hinfo s).1.symm)
    apply (hfp (pointTranscendenceSupport (x r))
      (pointTranscendenceSupport (x s)) (hsupp r) (hsupp s)
      ((hinfo r).2.1.trans (hinfo s).2.1.symm)).2.2
    rw [← hpivot r, ← hpivot s]
    exact hrs
  have hcurve : ∃ z, inRationalInterval (c.2.2.1 j) z ∧
      chartPoint c (Function.update (basisParameterMatrix idx 0) j z) ≠ x 0 := by
    obtain ⟨z, hz, hne⟩ := exists_chartCurve_point_ne (x 0)
      (selectedChartCoordinate select hselect (x 0) (hsupp 0))
    refine ⟨z, ?_, ?_⟩
    · simpa only [c, j] using hz
    · intro heq
      apply hne
      have hpkg := commonChartPackage_eq c (x 0) (hinfo 0).1
      have hparam : basisParameterMatrix idx 0 = pointChartParameters (x 0) := by
        have hsecond := (Sigma.ext_iff.mp hpkg).2
        exact eq_of_heq hsecond
      simpa only [c, j, hparam] using heq
  refine ⟨{
    chart := c
    pivot := j
    index := idx
    position := hpos
    box := hbox
    realizes := hrealizes
    unique := ?_
    derivative := ?_
    pivot_injective := hpivotInj
    curve_nonconstant := hcurve }⟩
  · simpa only [c] using pointChartParameters_unique (x 0)
  · simpa only [c] using pointChartParameters_derivative (x 0)

private theorem chartConfiguration_excluded_unique
    {m n : ℕ} [NeZero m]
    {x : Fin m → EuclideanSpace ℝ (Fin n)}
    (cfg : ChartConfiguration x) (r : Fin m)
    (p : Fin m × Fin cfg.chart.1)
    (h : cfg.index p.1 p.2 = cfg.index r cfg.pivot) :
    p = (r, cfg.pivot) := by
  have hpivot : p.2 = cfg.pivot := cfg.position p.1 r p.2 cfg.pivot h
  apply Prod.ext
  · apply cfg.pivot_injective
    simpa [hpivot] using h
  · exact hpivot

private theorem chartConfiguration_avoidsP3
    {n : ℕ} {x : Fin 3 → EuclideanSpace ℝ (Fin n)}
    (cfg : ChartConfiguration x) :
    distancePolynomial3 (x 0) (x 1) (x 2) ≠ 0 := by
  intro hzero
  let q : Fin 3 × Fin cfg.chart.1 := (2, cfg.pivot)
  let L : List (Fin 3 × Fin cfg.chart.1) := (Finset.univ.erase q).toList
  let idx' := normalizeIndices L cfg.index
  have hq0 : q.1 ≠ 0 := by simp [q]
  have hL : ∀ p ∈ L, p ≠ q := by
    intro p hp
    simpa [L] using hp
  have hexcluded : ∀ p : Fin 3 × Fin cfg.chart.1,
      cfg.index p.1 p.2 = cfg.index q.1 q.2 → p = q := by
    intro p hp
    simpa only [q] using chartConfiguration_excluded_unique cfg 2 p hp
  have hexcluded' := normalizeIndices_preserves_unique_excluded L cfg.index q hq0 hL hexcluded
  have hpos' : IndexPositionConsistent idx' :=
    normalizeIndices_position L cfg.position
  have hbox' : IndexMatrixInBox cfg.chart idx' :=
    normalizeIndices_box L cfg.position cfg.box
  have hzeroBase : distancePolynomial3
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 0))
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 1))
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 2)) = 0 := by
    rw [cfg.realizes 0, cfg.realizes 1, cfg.realizes 2]
    exact hzero
  have hzero' : distancePolynomial3
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart (basisParameterMatrix idx' 1))
      (chartPoint cfg.chart (basisParameterMatrix idx' 2)) = 0 :=
    distancePolynomial3_zero_normalizeIndices cfg.chart L cfg.index cfg.position cfg.box
      cfg.unique cfg.derivative hzeroBase
  obtain ⟨z, hz, hchanged⟩ := cfg.curve_nonconstant
  have hfinal := distancePolynomial3_zero_after_one_substitution cfg.chart
    (basisParameterMatrix idx') idx' (fun _ _ ↦ rfl) hpos' hbox'
    cfg.unique cfg.derivative 2 cfg.pivot hzero' hz
  have hnone (r : Fin 3) (hr : r ≠ 2) :
      ¬ ∃ l, idx' r l = idx' 2 cfg.pivot := by
    rintro ⟨l, hl⟩
    have hp := hexcluded'.2 (r, l) (hl.trans hexcluded'.1)
    exact hr (congrArg Prod.fst hp)
  have hrow1 : basisParameterMatrix idx' 1 = basisParameterMatrix idx' 0 := by
    funext l
    apply congrArg realTranscendenceBasisValue
    change normalizeIndices L cfg.index 1 l = normalizeIndices L cfg.index 0 l
    apply normalizeIndices_eq_of_mem L cfg.index (p := (1, l))
    simp [L, q]
  have hrow2 : Function.update (basisParameterMatrix idx' 2) cfg.pivot z =
      Function.update (basisParameterMatrix idx' 0) cfg.pivot z := by
    funext l
    by_cases hl : l = cfg.pivot
    · subst l
      simp
    · simp only [Function.update, hl, ↓reduceIte]
      apply congrArg realTranscendenceBasisValue
      change normalizeIndices L cfg.index 2 l = normalizeIndices L cfg.index 0 l
      apply normalizeIndices_eq_of_mem L cfg.index (p := (2, l))
      simp [L, q, hl]
  have hfinal' : distancePolynomial3
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart
        (Function.update (basisParameterMatrix idx' 0) cfg.pivot z)) = 0 := by
    change distancePolynomial3
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 2 cfg.pivot) z 0 l))
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 2 cfg.pivot) z 1 l))
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 2 cfg.pivot) z 2 l)) = 0 at hfinal
    rw [replaceBasisParameter_eq_self _ _ _ (hnone 0 (by decide)) z,
      replaceBasisParameter_eq_self _ _ _ (hnone 1 (by decide)) z,
      replaceBasisParameter_eq_update _ _ _ cfg.pivot hpos' rfl z,
      hrow1, hrow2] at hfinal
    exact hfinal
  have hsq : squaredDistance
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart
        (Function.update (basisParameterMatrix idx' 0) cfg.pivot z)) = 0 := by
    simpa [distancePolynomial3, squaredDistance] using hfinal'
  have heq : chartPoint cfg.chart
      (Function.update (basisParameterMatrix idx' 0) cfg.pivot z) =
      chartPoint cfg.chart (basisParameterMatrix idx' 0) := by
    by_contra hne
    exact squaredDistance_ne_zero (Ne.symm hne) hsq
  have hbase : basisParameterMatrix idx' 0 = basisParameterMatrix cfg.index 0 := by
    funext l
    apply congrArg realTranscendenceBasisValue
    exact normalizeIndices_base L cfg.index cfg.position l
  apply hchanged
  rw [← cfg.realizes 0, ← hbase]
  exact heq

private theorem chartConfiguration_avoidsP4
    {n : ℕ} {x : Fin 4 → EuclideanSpace ℝ (Fin n)}
    (cfg : ChartConfiguration x) :
    distancePolynomial4 (x 0) (x 1) (x 2) (x 3) ≠ 0 := by
  intro hzero
  let q : Fin 4 × Fin cfg.chart.1 := (1, cfg.pivot)
  let L : List (Fin 4 × Fin cfg.chart.1) := (Finset.univ.erase q).toList
  let idx' := normalizeIndices L cfg.index
  have hq0 : q.1 ≠ 0 := by simp [q]
  have hL : ∀ p ∈ L, p ≠ q := by
    intro p hp
    simpa [L] using hp
  have hexcluded : ∀ p : Fin 4 × Fin cfg.chart.1,
      cfg.index p.1 p.2 = cfg.index q.1 q.2 → p = q := by
    intro p hp
    simpa only [q] using chartConfiguration_excluded_unique cfg 1 p hp
  have hexcluded' := normalizeIndices_preserves_unique_excluded L cfg.index q hq0 hL hexcluded
  have hpos' : IndexPositionConsistent idx' :=
    normalizeIndices_position L cfg.position
  have hbox' : IndexMatrixInBox cfg.chart idx' :=
    normalizeIndices_box L cfg.position cfg.box
  have hzeroBase : distancePolynomial4
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 0))
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 1))
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 2))
      (chartPoint cfg.chart (basisParameterMatrix cfg.index 3)) = 0 := by
    rw [cfg.realizes 0, cfg.realizes 1, cfg.realizes 2, cfg.realizes 3]
    exact hzero
  have hzero' : distancePolynomial4
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart (basisParameterMatrix idx' 1))
      (chartPoint cfg.chart (basisParameterMatrix idx' 2))
      (chartPoint cfg.chart (basisParameterMatrix idx' 3)) = 0 :=
    distancePolynomial4_zero_normalizeIndices cfg.chart L cfg.index cfg.position cfg.box
      cfg.unique cfg.derivative hzeroBase
  obtain ⟨z, hz, hchanged⟩ := cfg.curve_nonconstant
  have hfinal := distancePolynomial4_zero_after_one_substitution cfg.chart
    (basisParameterMatrix idx') idx' (fun _ _ ↦ rfl) hpos' hbox'
    cfg.unique cfg.derivative 1 cfg.pivot hzero' hz
  have hnone (r : Fin 4) (hr : r ≠ 1) :
      ¬ ∃ l, idx' r l = idx' 1 cfg.pivot := by
    rintro ⟨l, hl⟩
    have hp := hexcluded'.2 (r, l) (hl.trans hexcluded'.1)
    exact hr (congrArg Prod.fst hp)
  have hrow2 : basisParameterMatrix idx' 2 = basisParameterMatrix idx' 0 := by
    funext l
    apply congrArg realTranscendenceBasisValue
    change normalizeIndices L cfg.index 2 l = normalizeIndices L cfg.index 0 l
    apply normalizeIndices_eq_of_mem L cfg.index (p := (2, l))
    simp [L, q]
  have hrow3 : basisParameterMatrix idx' 3 = basisParameterMatrix idx' 0 := by
    funext l
    apply congrArg realTranscendenceBasisValue
    change normalizeIndices L cfg.index 3 l = normalizeIndices L cfg.index 0 l
    apply normalizeIndices_eq_of_mem L cfg.index (p := (3, l))
    simp [L, q]
  have hrow1 : Function.update (basisParameterMatrix idx' 1) cfg.pivot z =
      Function.update (basisParameterMatrix idx' 0) cfg.pivot z := by
    funext l
    by_cases hl : l = cfg.pivot
    · subst l
      simp
    · simp only [Function.update, hl, ↓reduceIte]
      apply congrArg realTranscendenceBasisValue
      change normalizeIndices L cfg.index 1 l = normalizeIndices L cfg.index 0 l
      apply normalizeIndices_eq_of_mem L cfg.index (p := (1, l))
      simp [L, q, hl]
  have hfinal' : distancePolynomial4
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart
        (Function.update (basisParameterMatrix idx' 0) cfg.pivot z))
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart (basisParameterMatrix idx' 0)) = 0 := by
    change distancePolynomial4
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 1 cfg.pivot) z 0 l))
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 1 cfg.pivot) z 1 l))
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 1 cfg.pivot) z 2 l))
      (chartPoint cfg.chart (fun l ↦ replaceBasisParameter
        (basisParameterMatrix idx') idx' (idx' 1 cfg.pivot) z 3 l)) = 0 at hfinal
    rw [replaceBasisParameter_eq_self _ _ _ (hnone 0 (by decide)) z,
      replaceBasisParameter_eq_update _ _ _ cfg.pivot hpos' rfl z,
      replaceBasisParameter_eq_self _ _ _ (hnone 2 (by decide)) z,
      replaceBasisParameter_eq_self _ _ _ (hnone 3 (by decide)) z,
      hrow1, hrow2, hrow3] at hfinal
    exact hfinal
  have hsq : squaredDistance
      (chartPoint cfg.chart (basisParameterMatrix idx' 0))
      (chartPoint cfg.chart
        (Function.update (basisParameterMatrix idx' 0) cfg.pivot z)) = 0 := by
    simpa [distancePolynomial4, squaredDistance] using hfinal'
  have heq : chartPoint cfg.chart
      (Function.update (basisParameterMatrix idx' 0) cfg.pivot z) =
      chartPoint cfg.chart (basisParameterMatrix idx' 0) := by
    by_contra hne
    exact squaredDistance_ne_zero (Ne.symm hne) hsq
  have hbase : basisParameterMatrix idx' 0 = basisParameterMatrix cfg.index 0 := by
    funext l
    apply congrArg realTranscendenceBasisValue
    exact normalizeIndices_base L cfg.index cfg.position l
  apply hchanged
  rw [← cfg.realizes 0, ← hbase]
  exact heq

private theorem fin3_tuple_injective {X : Type*} {a b c : X}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem fin4_tuple_injective {X : Type*} {a b c d : X}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

private theorem fin3_has_other : ∀ r : Fin 3, ∃ s : Fin 3, s ≠ r := by
  intro r
  fin_cases r
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

private theorem fin4_has_other : ∀ r : Fin 4, ∃ s : Fin 4, s ≠ r := by
  intro r
  fin_cases r
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

/-- The all-dimensional Schmerl--Kunen master coloring, specialized to the two distance
polynomials needed for Problem 1127. -/
theorem distancePolynomialMasterColoring_of_continuumHypothesis
    (hCH : ContinuumHypothesis) (n : ℕ) :
    HasDistancePolynomialMasterColoring n := by
  obtain ⟨select, G, hselect, hfp⟩ :=
    exists_realTranscendenceSupportFingerprint hCH
  let color : EuclideanSpace ℝ (Fin n) → ℕ := masterColor select hselect G
  refine ⟨color, ?_, ?_⟩
  · intro a b c hab hac hnab hnac hnbc hzero
    let x : Fin 3 → EuclideanSpace ℝ (Fin n) := ![a, b, c]
    have hinj : Function.Injective x := by
      exact fin3_tuple_injective hnab hnac hnbc
    have hmono : ∀ r, masterColor select hselect G (x r) =
        masterColor select hselect G (x 0) := by
      intro r
      fin_cases r
      · rfl
      · exact hab.symm
      · exact hac.symm
    let cfg : ChartConfiguration x :=
      Classical.choice <| exists_chartConfiguration select G hselect hfp x hinj
        fin3_has_other hmono
    apply chartConfiguration_avoidsP3 cfg
    simpa [x] using hzero
  · intro a b c d hab hac had hnab hncd hnac hnad hnbc hnbd hzero
    let x : Fin 4 → EuclideanSpace ℝ (Fin n) := ![a, b, c, d]
    have hinj : Function.Injective x := by
      exact fin4_tuple_injective hnab hnac hnad hnbc hnbd hncd
    have hmono : ∀ r, masterColor select hselect G (x r) =
        masterColor select hselect G (x 0) := by
      intro r
      fin_cases r
      · rfl
      · exact hab.symm
      · exact hac.symm
      · exact had.symm
    let cfg : ChartConfiguration x :=
      Classical.choice <| exists_chartConfiguration select G hselect hfp x hinj
        fin4_has_other hmono
    apply chartConfiguration_avoidsP4 cfg
    simpa [x] using hzero

private abbrev HamelIndex := Module.Basis.ofVectorSpaceIndex ℚ ℝ

private noncomputable abbrev hamelBasis : Module.Basis HamelIndex ℚ ℝ :=
  Module.Basis.ofVectorSpace ℚ ℝ

private theorem hamelIndex_nonempty : Nonempty HamelIndex := by
  by_contra h
  have : IsEmpty HamelIndex := not_nonempty_iff.mp h
  have hz : (1 : ℝ) = 0 := by
    apply hamelBasis.repr.injective
    ext i
    exact isEmptyElim i
  exact one_ne_zero hz

private theorem hamelIndex_card_le_continuum : #HamelIndex ≤ Cardinal.continuum := by
  rw [← Cardinal.mk_real]
  exact Cardinal.mk_subtype_le _

/-- Under CH, the real line is the union of countably many sets whose nonzero parts are linearly
independent over `ℚ`.  Zero is alone in color zero. -/
theorem exists_linearlyIndependent_real_coloring (hCH : ContinuumHypothesis) :
    ∃ color : ℝ → ℕ,
      (∀ x, color x = 0 ↔ x = 0) ∧
      ∀ k : ℕ, LinearIndependent ℚ
        (fun x : {x : ℝ // color x = k ∧ x ≠ 0} ↦ x.1) := by
  have hI : #HamelIndex ≤ Cardinal.aleph 1 :=
    hamelIndex_card_le_continuum.trans_eq hCH
  obtain ⟨lo, wf, hcount⟩ := exists_wellOrder_countable_Iio hI
  let : LE HamelIndex := lo.toLE
  let : LT HamelIndex := lo.toLT
  let : Preorder HamelIndex := lo.toPreorder
  let : PartialOrder HamelIndex := lo.toPartialOrder
  let : LinearOrder HamelIndex := lo
  let : WellFoundedLT HamelIndex := wf
  let : Nonempty HamelIndex := hamelIndex_nonempty
  let pivot : ℝ → HamelIndex := maxBasisIndex hamelBasis
  let fiber : HamelIndex → Type := fun p ↦
    {x : ℝ // x ≠ 0 ∧ pivot x = p}
  have hIic (p : HamelIndex) : (Set.Iic p).Countable := by
    rw [← Set.Iio_insert]
    exact (hcount p).insert p
  have hFiber : ∀ p : HamelIndex, Countable (fiber p) := by
    intro p
    let v : Set.Iic p → ℝ := fun i ↦ hamelBasis i.1
    let S : Submodule ℚ ℝ := Submodule.span ℚ (Set.range v)
    let : Countable (Set.Iic p) := hIic p
    have hScount : Countable S := inferInstance
    rw [← Set.countable_univ_iff] at hScount
    let toS : fiber p → S := fun x ↦ ⟨x.1, by
      change x.1 ∈ Submodule.span ℚ (Set.range v)
      have hrange : Set.range v = hamelBasis '' Set.Iic p := by
        ext z
        simp [v]
      rw [hrange, hamelBasis.mem_span_image]
      intro i hi
      have hle : i ≤ pivot x.1 := support_le_maxBasisIndex hamelBasis x.2.1 hi
      rw [x.2.2] at hle
      exact hle⟩
    have htoS : Function.Injective toS := by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : S ↦ (z.1 : ℝ)) h
    exact htoS.countable
  let code : (p : HamelIndex) → fiber p ↪ ℕ := fun p ↦
    Classical.choice <| (Cardinal.le_def (fiber p) ℕ).mp <| by
      rw [Cardinal.mk_nat, Cardinal.mk_le_aleph0_iff]
      exact hFiber p
  let localCode : HamelIndex → ℝ → ℕ := fun p x ↦
    if hx : x ≠ 0 ∧ pivot x = p then code p ⟨x, hx⟩ else 0
  have localCode_injective (p : HamelIndex) {x y : ℝ}
      (hx0 : x ≠ 0) (hxp : pivot x = p)
      (hy0 : y ≠ 0) (hyp : pivot y = p)
      (hxy : localCode p x = localCode p y) : x = y := by
    have hx : x ≠ 0 ∧ pivot x = p := ⟨hx0, hxp⟩
    have hy : y ≠ 0 ∧ pivot y = p := ⟨hy0, hyp⟩
    have hcode : code p ⟨x, hx0, hxp⟩ = code p ⟨y, hy0, hyp⟩ := by
      simpa only [localCode, dif_pos hx, dif_pos hy] using hxy
    exact congrArg (fun z : fiber p ↦ z.1) ((code p).injective hcode)
  let color : ℝ → ℕ := fun x ↦ if hx : x = 0 then 0
    else localCode (pivot x) x + 1
  refine ⟨color, ?_, ?_⟩
  · intro x
    simp [color]
  · intro k
    apply linearIndependent_of_injective_maxBasisIndex hamelBasis
    · exact fun x ↦ x.2.2
    · intro x y hpivot
      apply Subtype.ext
      have hcolor : color x.1 = color y.1 := x.2.1.trans y.2.1.symm
      change pivot x.1 = pivot y.1 at hpivot
      have hencoded : localCode (pivot x.1) x.1 = localCode (pivot y.1) y.1 := by
        simpa only [color, dif_neg x.2.2, dif_neg y.2.2,
          Nat.add_left_inj] using hcolor
      rw [← hpivot] at hencoded
      exact localCode_injective (pivot x.1) x.2.2 rfl y.2.2 hpivot.symm hencoded

private theorem single_sub_single_eq {A : Type*} [DecidableEq A]
    {a b c d : A} (hab : a ≠ b) (hcd : c ≠ d)
    (h : (Finsupp.single a (1 : ℚ) - Finsupp.single b 1) =
      Finsupp.single c 1 - Finsupp.single d 1) : a = c ∧ b = d := by
  have ha := DFunLike.congr_fun h a
  have hac : a = c := by
    by_contra hac
    by_cases had : a = d
    · have hba : b ≠ a := Ne.symm hab
      have hca : c ≠ a := by simpa [had] using hcd
      have hbd : b ≠ d := fun hbd ↦ hab (had.trans hbd.symm)
      simp [Finsupp.single_apply, hac, had, hba, hca, hbd, hcd] at ha
      norm_num at ha
    · simp [Finsupp.single_apply, hab, hac, had] at ha
  subst c
  have hs : Finsupp.single b (1 : ℚ) = Finsupp.single d 1 := sub_right_inj.mp h
  have hbd : b = d := by
    by_contra hbd
    have hb := DFunLike.congr_fun hs b
    simp [Finsupp.single_apply, hbd] at hb
  exact ⟨rfl, hbd⟩

private theorem hasDistinctPairDistances_of_linearIndependentFibers
    {color : ℝ → ℕ} (hzero : ∀ x, color x = 0 ↔ x = 0)
    (hli : ∀ k : ℕ, LinearIndependent ℚ
      (fun x : {x : ℝ // color x = k ∧ x ≠ 0} ↦ x.1)) :
    HasDistinctPairDistances color := by
  intro x y u v hxy hxu hxv hnxy hnuv hdist
  have hx0 : x ≠ 0 := by
    intro hx
    have hy : y = 0 := (hzero y).mp (hxy.symm.trans ((hzero x).mpr hx))
    exact hnxy (hx.trans hy.symm)
  have hy0 : y ≠ 0 := by
    intro hy
    have hx : x = 0 := (hzero x).mp (hxy.trans ((hzero y).mpr hy))
    exact hnxy (hx.trans hy.symm)
  have hu0 : u ≠ 0 := by
    intro hu
    have hx : x = 0 := (hzero x).mp (hxu.trans ((hzero u).mpr hu))
    exact hx0 hx
  have hv0 : v ≠ 0 := by
    intro hv
    have hx : x = 0 := (hzero x).mp (hxv.trans ((hzero v).mpr hv))
    exact hx0 hx
  let X := {z : ℝ // color z = color x ∧ z ≠ 0}
  let sx : X := ⟨x, rfl, hx0⟩
  let sy : X := ⟨y, hxy.symm, hy0⟩
  let su : X := ⟨u, hxu.symm, hu0⟩
  let sv : X := ⟨v, hxv.symm, hv0⟩
  have hsxy : sx ≠ sy := fun h ↦ hnxy (congrArg Subtype.val h)
  have hsuv : su ≠ sv := fun h ↦ hnuv (congrArg Subtype.val h)
  have hinj := (linearIndependent_iff_injective_finsuppLinearCombination.mp (hli (color x)))
  rw [Real.dist_eq, Real.dist_eq, abs_eq_abs] at hdist
  rcases hdist with hpos | hneg
  · left
    have hcomb :
        Finsupp.linearCombination ℚ (fun z : X ↦ z.1)
            (Finsupp.single sx 1 - Finsupp.single sy 1) =
          Finsupp.linearCombination ℚ (fun z : X ↦ z.1)
            (Finsupp.single su 1 - Finsupp.single sv 1) := by
      simp [sx, sy, su, sv, hpos]
    have heq := single_sub_single_eq hsxy hsuv (hinj hcomb)
    exact ⟨congrArg Subtype.val heq.1, congrArg Subtype.val heq.2⟩
  · right
    have hcomb :
        Finsupp.linearCombination ℚ (fun z : X ↦ z.1)
            (Finsupp.single sx 1 - Finsupp.single sy 1) =
          Finsupp.linearCombination ℚ (fun z : X ↦ z.1)
            (Finsupp.single sv 1 - Finsupp.single su 1) := by
      simp [sx, sy, su, sv]
      linarith
    have heq := single_sub_single_eq hsxy (Ne.symm hsuv) (hinj hcomb)
    exact ⟨congrArg Subtype.val heq.1, congrArg Subtype.val heq.2⟩

/-- MAIN RESULT (dimension-one sufficiency): CH gives a countable coloring of the real line
with no repeated nondegenerate unordered-pair distance in a color class. -/
theorem real_coloring_of_continuumHypothesis (hCH : ContinuumHypothesis) :
    ∃ color : ℝ → ℕ, HasDistinctPairDistances color := by
  obtain ⟨color, hzero, hli⟩ := exists_linearlyIndependent_real_coloring hCH
  exact ⟨color, hasDistinctPairDistances_of_linearIndependentFibers hzero hli⟩

/-! ## The necessity of the continuum hypothesis

The following argument is a direct formalization of the sharp converse.  An embedded copy of
`ω₁` is translated by each real `x`.  Two members of each translate have the same color.  The
chosen indices, together with that color, determine `x`: otherwise two translated pairs would
have the same length in the same color class.  Thus `ℝ` injects into `ℕ × ω₁ × ω₁`, a set
of cardinality `ℵ₁`.
-/

/-- A canonical type of cardinality `ℵ₁`. -/
abbrev Omega1 : Type := (Cardinal.aleph.{0} 1).ord.ToType

private theorem mk_omega1 : #Omega1 = (Cardinal.aleph 1) := by
  exact Cardinal.mk_ord_toType _

private theorem omega1_uncountable : Uncountable Omega1 := by
  rw [← Cardinal.aleph0_lt_mk_iff, mk_omega1]
  exact Cardinal.aleph0_lt_aleph_one

private theorem exists_same_value (f : Omega1 → ℕ) :
    ∃ a b : Omega1, a ≠ b ∧ f a = f b := by
  let : Uncountable Omega1 := omega1_uncountable
  obtain ⟨k, hk⟩ := Cardinal.exists_uncountable_fiber f (by
    rw [Cardinal.mk_nat, mk_omega1]
    exact Cardinal.aleph0_lt_aleph_one)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (f ⁻¹' {k})
  refine ⟨a, b, ?_, ?_⟩
  · exact fun h ↦ hab (Subtype.ext h)
  · exact a.property.trans b.property.symm

private noncomputable def firstIndex (f : Omega1 → ℕ) : Omega1 :=
  (exists_same_value f).choose

private noncomputable def secondIndex (f : Omega1 → ℕ) : Omega1 :=
  (exists_same_value f).choose_spec.choose

private theorem chosen_indices_ne (f : Omega1 → ℕ) :
    firstIndex f ≠ secondIndex f :=
  (exists_same_value f).choose_spec.choose_spec.1

private theorem chosen_indices_same_value (f : Omega1 → ℕ) :
    f (firstIndex f) = f (secondIndex f) :=
  (exists_same_value f).choose_spec.choose_spec.2

private noncomputable def omega1EmbeddingReal : Omega1 ↪ ℝ :=
  Classical.choice <| Cardinal.le_def Omega1 ℝ |>.mp <| by
    rw [mk_omega1, Cardinal.mk_real]
    exact Cardinal.aleph_one_le_continuum

private noncomputable def translateFirst (color : ℝ → ℕ) (x : ℝ) : Omega1 :=
  firstIndex (fun a ↦ color (x + omega1EmbeddingReal a))

private noncomputable def translateSecond (color : ℝ → ℕ) (x : ℝ) : Omega1 :=
  secondIndex (fun a ↦ color (x + omega1EmbeddingReal a))

private noncomputable def translateCode (color : ℝ → ℕ) (x : ℝ) :
    ℕ × Omega1 × Omega1 :=
  (color (x + omega1EmbeddingReal (translateFirst color x)),
    translateFirst color x, translateSecond color x)

private theorem translate_indices_ne (color : ℝ → ℕ) (x : ℝ) :
    translateFirst color x ≠ translateSecond color x :=
  chosen_indices_ne _

private theorem translate_indices_same_color (color : ℝ → ℕ) (x : ℝ) :
    color (x + omega1EmbeddingReal (translateFirst color x)) =
      color (x + omega1EmbeddingReal (translateSecond color x)) :=
  chosen_indices_same_value (fun a ↦ color (x + omega1EmbeddingReal a))

private theorem translateCode_injective {color : ℝ → ℕ}
    (hcolor : HasDistinctPairDistances color) :
    Function.Injective (translateCode color) := by
  intro x y hxy
  have hfst : translateFirst color x = translateFirst color y := by
    exact congrArg (fun z : ℕ × Omega1 × Omega1 ↦ z.2.1) hxy
  have hsnd : translateSecond color x = translateSecond color y := by
    exact congrArg (fun z : ℕ × Omega1 × Omega1 ↦ z.2.2) hxy
  have hbase :
      color (x + omega1EmbeddingReal (translateFirst color x)) =
        color (y + omega1EmbeddingReal (translateFirst color y)) := by
    exact congrArg (fun z : ℕ × Omega1 × Omega1 ↦ z.1) hxy
  let a := omega1EmbeddingReal (translateFirst color x)
  let b := omega1EmbeddingReal (translateSecond color x)
  have hab : a ≠ b := by
    exact omega1EmbeddingReal.injective.ne (translate_indices_ne color x)
  have hsameX : color (x + a) = color (x + b) :=
    translate_indices_same_color color x
  have hsameY : color (y + a) = color (y + b) := by
    simpa [a, b, hfst, hsnd] using translate_indices_same_color color y
  have hbase' : color (x + a) = color (y + a) := by
    simpa [a, hfst] using hbase
  have hdist : dist (x + a) (x + b) = dist (y + a) (y + b) := by
    simp only [Real.dist_eq]
    congr 1 <;> ring
  have hneX : x + a ≠ x + b := add_left_cancel_iff.not.mpr hab
  have hneY : y + a ≠ y + b := add_left_cancel_iff.not.mpr hab
  rcases hcolor hsameX hbase' (hbase'.trans hsameY) hneX hneY hdist with h | h
  · linarith [h.1]
  · linarith [h.1, h.2]

private theorem mk_translateCode : #(ℕ × Omega1 × Omega1) = Cardinal.aleph 1 := by
  simp only [Cardinal.mk_prod, Cardinal.mk_nat, mk_omega1, Cardinal.lift_id]
  rw [Cardinal.aleph_mul_aleph, max_self, Cardinal.aleph0_mul_aleph]

/-- MAIN RESULT (sharp converse on the real line): a countable distinct-distance coloring of
the line implies the continuum hypothesis. -/
theorem continuumHypothesis_of_real_coloring {color : ℝ → ℕ}
    (hcolor : HasDistinctPairDistances color) : ContinuumHypothesis := by
  apply le_antisymm
  · rw [← Cardinal.mk_real, ← mk_translateCode]
    exact Cardinal.mk_le_of_injective (translateCode_injective hcolor)
  · exact Cardinal.aleph_one_le_continuum

private def linePoint (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 ![x]

private theorem linePoint_injective : Function.Injective linePoint := by
  intro x y h
  have h0 := congrFun (congrArg WithLp.ofLp h) 0
  simpa [linePoint] using h0

private theorem linePoint_dist (x y : ℝ) :
    dist (linePoint x) (linePoint y) = dist x y := by
  rw [dist_eq_norm, Real.dist_eq]
  simp [linePoint, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]

private def lineCoordinate (x : EuclideanSpace ℝ (Fin 1)) : ℝ :=
  x 0

private theorem lineCoordinate_injective : Function.Injective lineCoordinate := by
  intro x y hxy
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  exact hxy

private theorem lineCoordinate_dist (x y : EuclideanSpace ℝ (Fin 1)) :
    dist (lineCoordinate x) (lineCoordinate y) = dist x y := by
  rw [EuclideanSpace.dist_eq]
  simp [lineCoordinate, Real.dist_eq, Real.sqrt_sq_eq_abs]

private theorem pushforward_line {color : ℝ → ℕ}
    (hcolor : HasDistinctPairDistances color) :
    HasDistinctPairDistances (fun x : EuclideanSpace ℝ (Fin 1) ↦ color (lineCoordinate x)) := by
  intro x y u v hxy hxu hxv hnxy hnuv hdist
  have h := hcolor hxy hxu hxv
    (lineCoordinate_injective.ne hnxy) (lineCoordinate_injective.ne hnuv)
    (by simpa only [lineCoordinate_dist] using hdist)
  exact h.imp
    (fun h ↦ ⟨lineCoordinate_injective h.1, lineCoordinate_injective h.2⟩)
    (fun h ↦ ⟨lineCoordinate_injective h.1, lineCoordinate_injective h.2⟩)

/-- MAIN RESULT (Euclidean dimension one): CH yields the exact requested master coloring. -/
theorem distancePolynomialMasterColoring_one (hCH : ContinuumHypothesis) :
    HasDistancePolynomialMasterColoring 1 := by
  rw [hasDistancePolynomialMasterColoring_iff]
  obtain ⟨color, hcolor⟩ := real_coloring_of_continuumHypothesis hCH
  exact ⟨fun x ↦ color (lineCoordinate x), pushforward_line hcolor⟩

private theorem pullback_line {color : EuclideanSpace ℝ (Fin 1) → ℕ}
    (hcolor : HasDistinctPairDistances color) :
    HasDistinctPairDistances (fun x : ℝ ↦ color (linePoint x)) := by
  intro x y u v hxy hxu hxv hnxy hnuv hdist
  have h := hcolor hxy hxu hxv
    (linePoint_injective.ne hnxy) (linePoint_injective.ne hnuv)
    (by simpa only [linePoint_dist] using hdist)
  exact h.imp
    (fun h ↦ ⟨linePoint_injective h.1, linePoint_injective h.2⟩)
    (fun h ↦ ⟨linePoint_injective h.1, linePoint_injective h.2⟩)

/-- MAIN RESULT (necessity in Problem 1127): the asserted decompositions, already in dimension
one, imply the continuum hypothesis. -/
theorem erdos_1127_only_if (h : PositiveAnswer) : ContinuumHypothesis := by
  obtain ⟨color, hcolor⟩ := h 1
  exact continuumHypothesis_of_real_coloring (pullback_line hcolor)

/-- MAIN RESULT (all-dimensional sufficiency): under CH, every finite-dimensional Euclidean
space has a countable decomposition whose nondegenerate unordered-pair distances are all
distinct inside every cell. -/
theorem erdos_1127_if (hCH : ContinuumHypothesis) : PositiveAnswer := by
  rw [positiveAnswer_iff_distancePolynomialMasterColorings]
  exact distancePolynomialMasterColoring_of_continuumHypothesis hCH

/-- MAIN RESULT (complete resolution of Erdős Problem 1127): the requested decompositions in
all finite dimensions exist exactly under the continuum hypothesis. -/
theorem erdos_1127 : (𝔠 = (ℵ_ 1 : Cardinal.{0})) ↔ (∀ n : ℕ, ∃ color : EuclideanSpace ℝ (Fin n) → ℕ,
  Erdos1127.HasDistinctPairDistances color) :=
  ⟨erdos_1127_if, erdos_1127_only_if⟩

/-- The exact version of Problem 1127 on the real line. -/
def RealLineAnswer : Prop :=
  ∃ color : ℝ → ℕ, HasDistinctPairDistances color

/-- MAIN RESULT (Erdős--Kakutani/Davies on the line): the real line has a countable
distinct-distance decomposition exactly when the continuum hypothesis holds. -/
theorem erdos_1127_real_line : ContinuumHypothesis ↔ RealLineAnswer := by
  constructor
  · exact real_coloring_of_continuumHypothesis
  · rintro ⟨color, hcolor⟩
    exact continuumHypothesis_of_real_coloring hcolor

#print axioms erdos_1127_oriented_pair_formulation_false
#print axioms erdos_1127_degenerate_pair_formulation_false
#print axioms hasDistinctPairDistances_iff_avoidsP3_and_avoidsP4
#print axioms distancePolynomial3_strongOneAvoidable
#print axioms distancePolynomial4_strongOneAvoidable
#print axioms real_isRealClosed
#print axioms realAlgebraic_isRealClosed
#print axioms exists_realTranscendenceSupportFingerprint
#print axioms distancePolynomialMasterColoring_zero
#print axioms distancePolynomialMasterColoring_one
#print axioms distancePolynomialMasterColoring_of_continuumHypothesis
#print axioms erdos_1127_only_if
#print axioms erdos_1127_if
#print axioms erdos_1127
#print axioms erdos_1127_real_line

end Erdos1127
