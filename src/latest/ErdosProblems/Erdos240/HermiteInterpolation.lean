import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Finite Hermite interpolation with a quantitative remainder

This file supplies the analytic interpolation lemma used in the extrapolation
argument of van der Poorten--Loxton.  Repeated entries in `nodes` encode
derivative conditions.  The construction uses the (everywhere defined)
divided slope `dslope`; over `ℂ`, its apparent singularity is removable.
-/

open scoped BigOperators

open Complex Function Metric Polynomial Set

noncomputable section

namespace Erdos240.HermiteInterpolation

/-- The iterated divided difference associated to an ordered list of nodes. -/
def dividedDifference (f : ℂ → ℂ) : List ℂ → ℂ → ℂ
  | [], z => f z
  | a :: nodes, z => dividedDifference (dslope f a) nodes z

/-- The Newton--Hermite interpolation polynomial associated to an ordered list of nodes. -/
def polynomial (f : ℂ → ℂ) : List ℂ → ℂ[X]
  | [] => 0
  | a :: nodes => C (f a) + (X - C a) * polynomial (dslope f a) nodes

/-- The nodal product.  Repeated nodes occur with their list multiplicity. -/
def nodeProduct (nodes : List ℂ) (z : ℂ) : ℂ :=
  (nodes.map fun a => z - a).prod

/-- The absolute-value version of the nodal product. -/
def nodeProductNorm (nodes : List ℂ) (z : ℂ) : ℝ :=
  (nodes.map fun a => ‖z - a‖).prod

/-- Expand `(node, multiplicity)` data into the repeated-node list used by the construction. -/
def multiplicityNodes (data : List (ℂ × ℕ)) : List ℂ :=
  data.flatMap fun p => List.replicate p.2 p.1

@[simp] theorem dividedDifference_nil (f : ℂ → ℂ) : dividedDifference f [] = f := rfl

@[simp] theorem dividedDifference_cons (f : ℂ → ℂ) (a : ℂ) (nodes : List ℂ) :
    dividedDifference f (a :: nodes) = dividedDifference (dslope f a) nodes := rfl

@[simp] theorem polynomial_nil (f : ℂ → ℂ) : polynomial f [] = 0 := rfl

@[simp] theorem polynomial_cons (f : ℂ → ℂ) (a : ℂ) (nodes : List ℂ) :
    polynomial f (a :: nodes) =
      C (f a) + (X - C a) * polynomial (dslope f a) nodes := rfl

@[simp] theorem nodeProduct_nil (z : ℂ) : nodeProduct [] z = 1 := by
  simp [nodeProduct]

@[simp] theorem nodeProduct_cons (a : ℂ) (nodes : List ℂ) (z : ℂ) :
    nodeProduct (a :: nodes) z = (z - a) * nodeProduct nodes z := by
  simp [nodeProduct]

@[simp] theorem nodeProduct_append (left right : List ℂ) (z : ℂ) :
    nodeProduct (left ++ right) z = nodeProduct left z * nodeProduct right z := by
  simp [nodeProduct, List.map_append]

@[simp] theorem nodeProduct_replicate (m : ℕ) (a z : ℂ) :
    nodeProduct (List.replicate m a) z = (z - a) ^ m := by
  simp [nodeProduct]

@[simp] theorem norm_nodeProduct (nodes : List ℂ) (z : ℂ) :
    ‖nodeProduct nodes z‖ = nodeProductNorm nodes z := by
  induction nodes with
  | nil => simp [nodeProduct, nodeProductNorm]
  | cons a nodes ih =>
      rw [nodeProduct_cons, norm_mul, ih]
      rfl

theorem nodeProductNorm_nonneg (nodes : List ℂ) (z : ℂ) :
    0 ≤ nodeProductNorm nodes z := by
  induction nodes with
  | nil => simp [nodeProductNorm]
  | cons a nodes ih =>
      simp only [nodeProductNorm, List.map_cons, List.prod_cons]
      exact mul_nonneg (norm_nonneg _) ih

@[simp] theorem nodeProductNorm_cons (a : ℂ) (nodes : List ℂ) (z : ℂ) :
    nodeProductNorm (a :: nodes) z = ‖z - a‖ * nodeProductNorm nodes z := by
  simp [nodeProductNorm]

theorem nodeProduct_ne_zero_of_forall_ne {nodes : List ℂ} {z : ℂ}
    (h : ∀ a ∈ nodes, z ≠ a) : nodeProduct nodes z ≠ 0 := by
  induction nodes with
  | nil => simp
  | cons a nodes ih =>
      rw [nodeProduct_cons]
      exact mul_ne_zero (sub_ne_zero.2 (h a (by simp)))
        (ih fun b hb => h b (by simp [hb]))

theorem differentiable_nodeProduct (nodes : List ℂ) :
    Differentiable ℂ (nodeProduct nodes) := by
  induction nodes with
  | nil =>
      change Differentiable ℂ (fun _ : ℂ => 1)
      fun_prop
  | cons a nodes ih =>
      change Differentiable ℂ (fun z => (z - a) * nodeProduct nodes z)
      fun_prop

@[simp] theorem multiplicityNodes_nil : multiplicityNodes [] = [] := rfl

@[simp] theorem multiplicityNodes_cons (a : ℂ) (m : ℕ) (data : List (ℂ × ℕ)) :
    multiplicityNodes ((a, m) :: data) =
      List.replicate m a ++ multiplicityNodes data := by
  simp [multiplicityNodes]

@[simp] theorem multiplicityNodes_append (left right : List (ℂ × ℕ)) :
    multiplicityNodes (left ++ right) = multiplicityNodes left ++ multiplicityNodes right := by
  simp [multiplicityNodes, List.flatMap_append]

@[simp] theorem nodeProduct_multiplicityNodes (data : List (ℂ × ℕ)) (z : ℂ) :
    nodeProduct (multiplicityNodes data) z =
      (data.map fun p => (z - p.1) ^ p.2).prod := by
  induction data with
  | nil => simp
  | cons p data ih =>
      rcases p with ⟨a, m⟩
      simp [ih]

/-- Exact Newton remainder identity. -/
theorem eval_polynomial_add_remainder (f : ℂ → ℂ) (nodes : List ℂ) (z : ℂ) :
    (polynomial f nodes).eval z +
        nodeProduct nodes z * dividedDifference f nodes z = f z := by
  induction nodes generalizing f with
  | nil => simp
  | cons a nodes ih =>
      have hslope : (z - a) * dslope f a z = f z - f a := by
        simpa [smul_eq_mul] using sub_smul_dslope f a z
      rw [polynomial_cons, eval_add, eval_C, eval_mul, eval_sub, eval_X, eval_C,
        nodeProduct_cons, dividedDifference_cons]
      calc
        f a + (z - a) * (polynomial (dslope f a) nodes).eval z +
              (z - a) * nodeProduct nodes z * dividedDifference (dslope f a) nodes z =
            f a + (z - a) *
              ((polynomial (dslope f a) nodes).eval z +
                nodeProduct nodes z * dividedDifference (dslope f a) nodes z) := by ring
        _ = f a + (z - a) * dslope f a z := by rw [ih (dslope f a)]
        _ = f z := by rw [hslope]; ring

/-- Subtractive form of the exact Newton remainder identity. -/
theorem remainder_eq_product_mul_dividedDifference (f : ℂ → ℂ)
    (nodes : List ℂ) (z : ℂ) :
    f z - (polynomial f nodes).eval z =
      nodeProduct nodes z * dividedDifference f nodes z := by
  rw [← eval_polynomial_add_remainder f nodes z]
  ring

/-- Iterated divided differences of an entire function are entire. -/
theorem differentiable_dividedDifference {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (nodes : List ℂ) : Differentiable ℂ (dividedDifference f nodes) := by
  induction nodes generalizing f with
  | nil => simpa using hf
  | cons a nodes ih =>
      apply ih
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (s := Set.univ) (by simp)).2
        hf.differentiableOn

/-- If the list contains a block of `m` copies of `a`, the Newton--Hermite polynomial agrees with
`f` through derivative order `m - 1` at `a`.  The lists before and after the block may contain
arbitrary additional nodes. -/
theorem iteratedDeriv_eval_polynomial_eq_of_replicate_block
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (before after : List ℂ)
    (a : ℂ) (m k : ℕ) (hk : k < m) :
    iteratedDeriv k (fun z => (polynomial f
      (before ++ List.replicate m a ++ after)).eval z) a = iteratedDeriv k f a := by
  let nodes := before ++ List.replicate m a ++ after
  let P : ℂ[X] := polynomial f nodes
  let D : ℂ → ℂ := dividedDifference f nodes
  let Q : ℂ → ℂ := fun z =>
    nodeProduct before z * nodeProduct after z * D z
  have hPdiff : Differentiable ℂ (fun z => P.eval z) := Polynomial.differentiable _
  have hDdiff : Differentiable ℂ D := differentiable_dividedDifference hf nodes
  have hQdiff : Differentiable ℂ Q := by
    dsimp only [Q]
    exact ((differentiable_nodeProduct before).mul
      (differentiable_nodeProduct after)).mul hDdiff
  have hQanalytic : AnalyticAt ℂ Q a := hQdiff.analyticAt a
  have hrem_analytic : AnalyticAt ℂ (fun z => f z - P.eval z) a :=
    (hf.analyticAt a).sub (hPdiff.analyticAt a)
  have hfactor : ∀ z, f z - P.eval z = (z - a) ^ m * Q z := by
    intro z
    rw [remainder_eq_product_mul_dividedDifference]
    simp only [nodes, nodeProduct_append, nodeProduct_replicate, D, Q]
    ring
  have horder : (m : ℕ∞) ≤ analyticOrderAt (fun z => f z - P.eval z) a :=
    (natCast_le_analyticOrderAt hrem_analytic).2
      ⟨Q, hQanalytic, Filter.Eventually.of_forall hfactor⟩
  have hzero : iteratedDeriv k (fun z => f z - P.eval z) a = 0 :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hrem_analytic).1 horder k hk
  rw [iteratedDeriv_fun_sub (hf.contDiff.contDiffAt) (hPdiff.contDiff.contDiffAt)] at hzero
  have heq : iteratedDeriv k f a = iteratedDeriv k (fun z => P.eval z) a :=
    sub_eq_zero.mp hzero
  simpa [P, nodes] using heq.symm

/-- The derivative-matching statement in explicit `(node, multiplicity)` notation. -/
theorem iteratedDeriv_eval_polynomial_multiplicityNodes
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (before after : List (ℂ × ℕ)) (a : ℂ) (m k : ℕ) (hk : k < m) :
    iteratedDeriv k (fun z =>
      (polynomial f (multiplicityNodes (before ++ (a, m) :: after))).eval z) a =
        iteratedDeriv k f a := by
  simpa using iteratedDeriv_eval_polynomial_eq_of_replicate_block hf
    (multiplicityNodes before) (multiplicityNodes after) a m k hk

/-- The interpolation polynomial has degree strictly less than the number of nodes, unless it is
zero (the disjunction also covers the empty list). -/
theorem polynomial_eq_zero_or_natDegree_lt (f : ℂ → ℂ) (nodes : List ℂ) :
    polynomial f nodes = 0 ∨ (polynomial f nodes).natDegree < nodes.length := by
  induction nodes generalizing f with
  | nil => simp
  | cons a nodes ih =>
      rcases ih (dslope f a) with hzero | hdeg
      · simp [polynomial_cons, hzero]
      · by_cases hP : polynomial f (a :: nodes) = 0
        · exact Or.inl hP
        · refine Or.inr ?_
          rw [polynomial_cons]
          calc
            (C (f a) + (X - C a) * polynomial (dslope f a) nodes).natDegree
                ≤ max (C (f a)).natDegree
                    (((X - C a) * polynomial (dslope f a) nodes).natDegree) :=
              natDegree_add_le _ _
            _ ≤ max 0 (1 + (polynomial (dslope f a) nodes).natDegree) := by
              gcongr
              · rw [natDegree_C]
              · calc
                  ((X - C a) * polynomial (dslope f a) nodes).natDegree
                      ≤ (X - C a).natDegree +
                          (polynomial (dslope f a) nodes).natDegree := natDegree_mul_le
                  _ ≤ 1 + (polynomial (dslope f a) nodes).natDegree := by
                    gcongr
                    exact natDegree_X_sub_C_le _
            _ < (a :: nodes).length := by simp only [List.length_cons]; omega

/-- Integral form of the Hermite remainder.  This is Cauchy's formula applied to the entire
divided difference; on the boundary the exact Newton identity replaces it by
`(f - P) / nodeProduct`. -/
theorem remainder_eq_nodeProduct_mul_circleIntegral
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : List ℂ)
    {c z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ ball c R)
    (hnodes : ∀ a ∈ nodes, a ∈ ball c R) :
    f z - (polynomial f nodes).eval z = nodeProduct nodes z *
      ((2 * Real.pi * I : ℂ)⁻¹ *
        ∮ w in C(c, R), (w - z)⁻¹ *
          ((nodeProduct nodes w)⁻¹ * (f w - (polynomial f nodes).eval w))) := by
  let D : ℂ → ℂ := dividedDifference f nodes
  have hDdiff : Differentiable ℂ D := differentiable_dividedDifference hf nodes
  have hcongr :
      (∮ w in C(c, R), (w - z)⁻¹ *
          ((nodeProduct nodes w)⁻¹ * (f w - (polynomial f nodes).eval w))) =
        ∮ w in C(c, R), (w - z)⁻¹ • D w := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have hw_ne (a : ℂ) (ha : a ∈ nodes) : w ≠ a :=
      Metric.sphere_disjoint_ball.ne_of_mem hw (hnodes a ha)
    have hWne : nodeProduct nodes w ≠ 0 :=
      nodeProduct_ne_zero_of_forall_ne hw_ne
    change (w - z)⁻¹ *
        ((nodeProduct nodes w)⁻¹ * (f w - (polynomial f nodes).eval w)) =
      (w - z)⁻¹ * D w
    rw [remainder_eq_product_mul_dividedDifference]
    simp [D, hWne]
  have hcauchy :
      (∮ w in C(c, R), (w - z)⁻¹ • D w) = (2 * Real.pi * I : ℂ) • D z :=
    hDdiff.differentiableOn.circleIntegral_sub_inv_smul hz
  rw [remainder_eq_product_mul_dividedDifference, hcongr, hcauchy]
  change nodeProduct nodes z * D z = nodeProduct nodes z *
    ((2 * Real.pi * I : ℂ)⁻¹ * ((2 * Real.pi * I : ℂ) * D z))
  field_simp [two_pi_I_ne_zero]

/-- Quantitative Hermite remainder estimate on a disc.  The hypothesis is the explicit boundary
quotient bound

`‖f(w) - P(w)‖ / ∏ a ∈ nodes, ‖w-a‖ ≤ B`.

The conclusion exhibits both the product of target-to-node distances and the Cauchy denominator
`R - dist z c`.  Repeated entries in `nodes` therefore contribute their full multiplicity. -/
theorem norm_remainder_le_of_boundary_div_nodeProductNorm
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (nodes : List ℂ)
    {c z : ℂ} {R B : ℝ} (hR : 0 < R) (hz : z ∈ ball c R)
    (hB : 0 ≤ B) (hnodes : ∀ a ∈ nodes, a ∈ ball c R)
    (hboundary : ∀ w ∈ sphere c R,
      ‖f w - (polynomial f nodes).eval w‖ / nodeProductNorm nodes w ≤ B) :
    ‖f z - (polynomial f nodes).eval z‖ ≤
      nodeProductNorm nodes z * (R * (B / (R - dist z c))) := by
  let P : ℂ[X] := polynomial f nodes
  let D : ℂ → ℂ := dividedDifference f nodes
  have hDdiff : Differentiable ℂ D := differentiable_dividedDifference hf nodes
  have hdelta : 0 < R - dist z c := by
    rw [mem_ball] at hz
    linarith
  have hD_boundary : ∀ w ∈ sphere c R, ‖D w‖ ≤ B := by
    intro w hw
    have hw_ne (a : ℂ) (ha : a ∈ nodes) : w ≠ a :=
      Metric.sphere_disjoint_ball.ne_of_mem hw (hnodes a ha)
    have hWne : nodeProduct nodes w ≠ 0 :=
      nodeProduct_ne_zero_of_forall_ne hw_ne
    have hWpos : 0 < nodeProductNorm nodes w := by
      rw [← norm_nodeProduct]
      exact norm_pos_iff.mpr hWne
    have heq : ‖D w‖ =
        ‖f w - P.eval w‖ / nodeProductNorm nodes w := by
      rw [remainder_eq_product_mul_dividedDifference, norm_mul, norm_nodeProduct]
      exact (mul_div_cancel_left₀ ‖D w‖ hWpos.ne').symm
    rw [heq]
    exact hboundary w hw
  have hkernel : ∀ w ∈ sphere c R,
      ‖(w - z)⁻¹ • D w‖ ≤ B / (R - dist z c) := by
    intro w hw
    have hdist : R - dist z c ≤ ‖w - z‖ := by
      have hwR : dist w c = R := mem_sphere.mp hw
      rw [← dist_eq_norm]
      linarith [dist_triangle w z c]
    rw [norm_smul, norm_inv]
    rw [inv_mul_eq_div, div_le_div_iff₀ (lt_of_lt_of_le hdelta hdist) hdelta]
    exact mul_le_mul (hD_boundary w hw) hdist hdelta.le hB
  have hcauchy :
      (∮ w in C(c, R), (w - z)⁻¹ • D w) = (2 * Real.pi * I : ℂ) • D z :=
    hDdiff.differentiableOn.circleIntegral_sub_inv_smul hz
  have hDnorm : ‖D z‖ ≤ R * (B / (R - dist z c)) := by
    have hIntegral :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hkernel
    rw [hcauchy, inv_smul_smul₀ two_pi_I_ne_zero] at hIntegral
    exact hIntegral
  rw [remainder_eq_product_mul_dividedDifference, norm_mul, norm_nodeProduct]
  exact mul_le_mul_of_nonneg_left hDnorm (nodeProductNorm_nonneg nodes z)

end Erdos240.HermiteInterpolation
