import ErdosProblems.Erdos88.GraphLinearCancellation
import ErdosProblems.Erdos88.GaussianQuadratic

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace Erdos88

lemma abs_exp_neg_sub_exp_neg_le_of_le {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ b - a := by
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hfactor :
      Real.exp (-a) - Real.exp (-b) =
        Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
    rw [show -b = -a + -(b - a) by ring, Real.exp_add]
    ring
  have hsecond : 0 ≤ 1 - Real.exp (-(b - a)) := by
    rw [sub_nonneg]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hfirst : Real.exp (-a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hlinear : 1 - Real.exp (-(b - a)) ≤ b - a := by
    linarith [Real.one_sub_le_exp_neg (b - a)]
  rw [hfactor, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hsecond]
  calc
    Real.exp (-a) * (1 - Real.exp (-(b - a))) ≤
        1 * (1 - Real.exp (-(b - a))) :=
      mul_le_mul_of_nonneg_right hfirst hsecond
    _ ≤ b - a := by simpa using hlinear

lemma abs_exp_neg_sub_exp_neg_le {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · simpa [abs_of_nonpos (sub_nonpos.mpr hab)] using
      abs_exp_neg_sub_exp_neg_le_of_le ha hab
  · have hba : b ≤ a := le_of_not_ge hab
    simpa [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hba)] using
      abs_exp_neg_sub_exp_neg_le_of_le hb hba

namespace GraphQuadratic

open Classical

/-- Equation (4.34) in the coefficient normalization used by the Gaussian
comparison: total variance is linear Gaussian variance plus the edge term. -/
lemma graphPerturbedSigma_sq_eq_linear_add_edge {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) :
    graphPerturbedSigma G e₀ c ^ 2 =
      BooleanSlices.vectorSqNorm (graphSliceLinear G c) +
        (G.edgeFinset.card : ℝ) / 16 := by
  rw [graphPerturbedSigma_sq, variance_half_perturbedEdgePolynomial,
    vectorSqNorm_graphSliceLinear]

/-- The centered Gaussian linear approximation differs from the standard
normal characteristic function only through the edge contribution in
equation (4.34). -/
lemma norm_centeredGraphLinearGaussian_sub_standardNormalChar_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (hσ : 0 < graphPerturbedSigma G e₀ c) (t : ℝ) :
    ‖Complex.exp (-((((t / graphPerturbedSigma G e₀ c) ^ 2 *
          BooleanSlices.vectorSqNorm (graphSliceLinear G c) / 2 : ℝ) : ℂ))) -
        GaussianQuadratic.standardNormalChar t‖ ≤
      t ^ 2 * (G.edgeFinset.card : ℝ) /
        (32 * graphPerturbedSigma G e₀ c ^ 2) := by
  let σ := graphPerturbedSigma G e₀ c
  let V := BooleanSlices.vectorSqNorm (graphSliceLinear G c)
  let E : ℝ := G.edgeFinset.card
  have hσ' : 0 < σ := hσ
  have hV : 0 ≤ V := by
    dsimp only [V, BooleanSlices.vectorSqNorm]
    positivity
  have hE : 0 ≤ E := by positivity
  have hdecomp : σ ^ 2 = V + E / 16 := by
    exact graphPerturbedSigma_sq_eq_linear_add_edge G e₀ c
  let a := (t / σ) ^ 2 * V / 2
  let b := t ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : |a - b| = t ^ 2 * E / (32 * σ ^ 2) := by
    have hdiff : a - b = -(t ^ 2 * E / (32 * σ ^ 2)) := by
      dsimp [a, b]
      field_simp [hσ'.ne']
      nlinarith [hdecomp]
    rw [hdiff, abs_neg, abs_of_nonneg]
    positivity
  have hrealA :
      Complex.exp (-((a : ℝ) : ℂ)) = ((Real.exp (-a) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
  have hrealB :
      GaussianQuadratic.standardNormalChar t =
        ((Real.exp (-b) : ℝ) : ℂ) := by
    unfold GaussianQuadratic.standardNormalChar
    congr 2
    dsimp only [b]
    ring
  change ‖Complex.exp (-((a : ℝ) : ℂ)) -
      GaussianQuadratic.standardNormalChar t‖ ≤ _
  rw [hrealA, hrealB, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  calc
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| :=
      abs_exp_neg_sub_exp_neg_le ha hb
    _ = t ^ 2 * E / (32 * σ ^ 2) := hab

/-- At normalized frequency `t / σ`, the centered graph Gaussian quadratic
is close to the standard normal characteristic function.  The two terms are
respectively the quadratic `L¹` error and the exact variance mismatch. -/
theorem norm_centeredGraphGaussianQuadratic_sub_standardNormalChar_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (hσ : 0 < graphPerturbedSigma G e₀ c) (t : ℝ) :
    ‖Complex.exp (-(((((t / graphPerturbedSigma G e₀ c) *
          graphSliceConstant G e₀ c : ℝ) : ℂ) * Complex.I))) *
          BooleanSlices.gaussianQuadraticCharacteristic
            (graphSliceConstant G e₀ c) (graphSliceLinear G c)
            (graphSliceMatrix G) (t / graphPerturbedSigma G e₀ c) -
        GaussianQuadratic.standardNormalChar t‖ ≤
      |t / graphPerturbedSigma G e₀ c| *
          √((G.edgeFinset.card : ℝ) / 16) +
        t ^ 2 * (G.edgeFinset.card : ℝ) /
          (32 * graphPerturbedSigma G e₀ c ^ 2) := by
  let σ := graphPerturbedSigma G e₀ c
  let qchar := BooleanSlices.gaussianQuadraticCharacteristic
      (graphSliceConstant G e₀ c) (graphSliceLinear G c)
      (graphSliceMatrix G) (t / σ)
  let lchar : ℂ := Complex.exp (-((((t / σ) ^ 2 *
      BooleanSlices.vectorSqNorm (graphSliceLinear G c) / 2 : ℝ) : ℂ)))
  have hquad := norm_centeredGraphGaussianQuadratic_sub_linearGaussian_le
    G e₀ c (t / σ)
  have hlin := norm_centeredGraphLinearGaussian_sub_standardNormalChar_le
    G e₀ c hσ t
  change ‖Complex.exp (-(((((t / σ) * graphSliceConstant G e₀ c : ℝ) : ℂ) *
      Complex.I))) * qchar - GaussianQuadratic.standardNormalChar t‖ ≤ _
  calc
    ‖Complex.exp (-(((((t / σ) * graphSliceConstant G e₀ c : ℝ) : ℂ) *
          Complex.I))) * qchar - GaussianQuadratic.standardNormalChar t‖ ≤
        ‖Complex.exp (-(((((t / σ) * graphSliceConstant G e₀ c : ℝ) : ℂ) *
              Complex.I))) * qchar - lchar‖ +
          ‖lchar - GaussianQuadratic.standardNormalChar t‖ := by
      rw [show Complex.exp (-(((((t / σ) * graphSliceConstant G e₀ c : ℝ) : ℂ) *
              Complex.I))) * qchar - GaussianQuadratic.standardNormalChar t =
          (Complex.exp (-(((((t / σ) * graphSliceConstant G e₀ c : ℝ) : ℂ) *
              Complex.I))) * qchar - lchar) +
            (lchar - GaussianQuadratic.standardNormalChar t) by ring]
      exact norm_add_le _ _
    _ ≤ |t / σ| * √((G.edgeFinset.card : ℝ) / 16) +
          t ^ 2 * (G.edgeFinset.card : ℝ) / (32 * σ ^ 2) :=
      add_le_add hquad hlin

/-- The exact normalized characteristic-function comparison obtained by
combining the quadratic invariance estimate with Gaussian linear
cancellation.  This is the quantitative core of KSSS Lemma 7.1 before its
elementary scale simplification. -/
theorem norm_centeredGraphCharacteristic_sub_standardNormalChar_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hn : 1 ≤ n)
    (hf : ∀ i, |graphSliceLinear G c i| ≤
      BooleanSlices.scale n (1 / 2 + 3 * δ))
    (hσ : 0 < graphPerturbedSigma G e₀ c) (t : ℝ) :
    ‖Complex.exp (-(((((t / graphPerturbedSigma G e₀ c) *
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) *
          Complex.I))) *
          BooleanSlices.finiteCharacteristic
            (Probability.perturbedEdgePolynomial G e₀ c)
            (t / graphPerturbedSigma G e₀ c) -
        GaussianQuadratic.standardNormalChar t‖ ≤
      (675 / 2 : ℝ) * |t / graphPerturbedSigma G e₀ c| ^ 4 *
          BooleanSlices.scale n (3 + 12 * δ) +
        (|t / graphPerturbedSigma G e₀ c| *
            √((G.edgeFinset.card : ℝ) / 16) +
          t ^ 2 * (G.edgeFinset.card : ℝ) /
            (32 * graphPerturbedSigma G e₀ c ^ 2)) := by
  let σ := graphPerturbedSigma G e₀ c
  let τ := t / σ
  let μ := graphSliceConstant G e₀ c
  let P := Probability.perturbedEdgePolynomial G e₀ c
  let Q := BooleanSlices.sliceQuadratic μ (graphSliceLinear G c)
      (graphSliceMatrix G)
  let phase := Complex.exp (-((((τ * μ : ℝ) : ℂ) * Complex.I)))
  let sliceChar := BooleanSlices.finiteCharacteristic Q τ
  let gaussChar := BooleanSlices.gaussianQuadraticCharacteristic μ
      (graphSliceLinear G c) (graphSliceMatrix G) τ
  have hQ : Q = P := by
    funext W
    exact sliceQuadratic_graph_coefficients G e₀ c W
  have hQactual : Q = Probability.perturbedEdgePolynomial G e₀ c := hQ
  have hμ : μ = Probability.expectation (1 / 2 : ℝ) P := by
    exact graphSliceConstant_eq_expectation_half G e₀ c
  have hsliceRaw := BooleanSlices.norm_sliceCharacteristic_sub_gaussianQuadratic_le
    δ hδ hn μ (graphSliceLinear G c) (graphSliceMatrix G) hf
      (graphSliceMatrix_abs_le_one G) τ
  have hslice :
      ‖sliceChar - gaussChar‖ ≤
        (675 / 2 : ℝ) * |τ| ^ 4 *
          BooleanSlices.scale n (3 + 12 * δ) := by
    have hdiag : (∑ i, graphSliceMatrix G i i ^ 2) = 0 := by
      simp only [graphSliceMatrix_diagonal, zero_pow (by norm_num : 2 ≠ 0),
        Finset.sum_const_zero]
    rw [hdiag, mul_zero, Real.sqrt_zero, mul_zero, add_zero] at hsliceRaw
    dsimp only [sliceChar, gaussChar, Q]
    convert hsliceRaw using 1 <;> ring
  have hphase : ‖phase‖ = 1 := by
    dsimp only [phase]
    rw [Complex.norm_exp]
    simp
  have hgauss :=
    norm_centeredGraphGaussianQuadratic_sub_standardNormalChar_le
      G e₀ c hσ t
  rw [← hμ, ← hQactual]
  change ‖phase * sliceChar - GaussianQuadratic.standardNormalChar t‖ ≤ _
  calc
    ‖phase * sliceChar - GaussianQuadratic.standardNormalChar t‖ ≤
        ‖phase * (sliceChar - gaussChar)‖ +
          ‖phase * gaussChar - GaussianQuadratic.standardNormalChar t‖ := by
      rw [show phase * sliceChar - GaussianQuadratic.standardNormalChar t =
          phase * (sliceChar - gaussChar) +
            (phase * gaussChar - GaussianQuadratic.standardNormalChar t) by ring]
      exact norm_add_le _ _
    _ ≤ (675 / 2 : ℝ) * |τ| ^ 4 *
          BooleanSlices.scale n (3 + 12 * δ) +
        (|τ| * √((G.edgeFinset.card : ℝ) / 16) +
          t ^ 2 * (G.edgeFinset.card : ℝ) / (32 * σ ^ 2)) := by
      apply add_le_add
      · rw [norm_mul, hphase, one_mul]
        exact hslice
      · exact hgauss

lemma edgeFinset_card_cast_le_sq {n : ℕ} (G : SimpleGraph (Fin n)) :
    (G.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hedgeNat : G.edgeFinset.card ≤ n ^ 2 := by
    calc
      G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 :=
        G.card_edgeFinset_le_card_choose_two
      _ = n.choose 2 := by simp
      _ ≤ n ^ 2 := Nat.choose_le_pow n 2
  exact_mod_cast hedgeNat

lemma scale_three_halves_eq_mul_sqrt {n : ℕ} (hn : 0 < n) :
    BooleanSlices.scale n (3 / 2 : ℝ) = (n : ℝ) * √(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold BooleanSlices.scale
  calc
    (n : ℝ) ^ (3 / 2 : ℝ) =
        (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
      exact Real.rpow_add hnR 1 (1 / 2)
    _ = (n : ℝ) * √(n : ℝ) := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma sqrt_edge_card_div_sixteen_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    √((G.edgeFinset.card : ℝ) / 16) ≤ (n : ℝ) / 4 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hedge := edgeFinset_card_cast_le_sq G
    nlinarith

lemma invariance_scale_bound_one_fifth {n : ℕ}
    (σ a t : ℝ) (hn : 1 ≤ n) (ha : 0 < a) (hσ : 0 < σ)
    (hσLower : (a / 2) * BooleanSlices.scale n (3 / 2) ≤ σ)
    (ht : |t| ≤ BooleanSlices.scale n (1 / 30)) :
    (675 / 2 : ℝ) * |t / σ| ^ 4 * BooleanSlices.scale n (27 / 5) ≤
      (5400 / a ^ 4) * |t| / √(n : ℝ) := by
  let q := |t|
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hq : 0 ≤ q := abs_nonneg t
  have hscale32 : 0 < BooleanSlices.scale n (3 / 2) :=
    BooleanSlices.scale_pos hnPos _
  have hbase : 0 ≤ (a / 2) * BooleanSlices.scale n (3 / 2) := by positivity
  have hσ4 : ((a / 2) * BooleanSlices.scale n (3 / 2)) ^ 4 ≤ σ ^ 4 :=
    pow_le_pow_left₀ hbase hσLower 4
  have hq3 : q ^ 3 ≤ BooleanSlices.scale n (1 / 10) := by
    have hp := pow_le_pow_left₀ hq ht 3
    calc
      q ^ 3 ≤ BooleanSlices.scale n (1 / 30) ^ 3 := hp
      _ = BooleanSlices.scale n (1 / 10) := by
        rw [show BooleanSlices.scale n (1 / 30) ^ 3 =
            (BooleanSlices.scale n (1 / 30) *
              BooleanSlices.scale n (1 / 30)) *
              BooleanSlices.scale n (1 / 30) by ring,
          BooleanSlices.scale_mul hnPos,
          BooleanSlices.scale_mul hnPos]
        congr 1
        ring
  have hnum : q ^ 4 * BooleanSlices.scale n (27 / 5) ≤
      q * BooleanSlices.scale n (11 / 2) := by
    calc
      q ^ 4 * BooleanSlices.scale n (27 / 5) =
          q * (q ^ 3 * BooleanSlices.scale n (27 / 5)) := by ring
      _ ≤ q * (BooleanSlices.scale n (1 / 10) *
          BooleanSlices.scale n (27 / 5)) := by
        gcongr
        exact BooleanSlices.scale_nonneg n _
      _ = q * BooleanSlices.scale n (11 / 2) := by
        rw [BooleanSlices.scale_mul hnPos]
        congr 2
        ring
  have hsqrtPos : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hnPos)
  have hscale6 : 0 < BooleanSlices.scale n 6 :=
    BooleanSlices.scale_pos hnPos _
  have hsqrtScale : √(n : ℝ) = BooleanSlices.scale n (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rfl
  have hscaleProduct : √(n : ℝ) * BooleanSlices.scale n (11 / 2) =
      BooleanSlices.scale n 6 := by
    rw [hsqrtScale, BooleanSlices.scale_mul hnPos]
    congr 1
    ring
  have hratio : q ^ 4 * BooleanSlices.scale n (27 / 5) /
        BooleanSlices.scale n 6 ≤ q / √(n : ℝ) := by
    rw [div_le_iff₀ hscale6]
    calc
      q ^ 4 * BooleanSlices.scale n (27 / 5) ≤
          q * BooleanSlices.scale n (11 / 2) := hnum
      _ = q / √(n : ℝ) * BooleanSlices.scale n 6 := by
        rw [← hscaleProduct]
        field_simp [hsqrtPos.ne']
  have hdenom :
      (a / 2 * BooleanSlices.scale n (3 / 2)) ^ 4 =
        a ^ 4 / 16 * BooleanSlices.scale n 6 := by
    have hscalePow : BooleanSlices.scale n (3 / 2) ^ 4 =
        BooleanSlices.scale n 6 := by
      unfold BooleanSlices.scale
      calc
        ((n : ℝ) ^ (3 / 2 : ℝ)) ^ 4 =
            (n : ℝ) ^ ((3 / 2 : ℝ) * (4 : ℝ)) :=
          (Real.rpow_mul_natCast (x := (n : ℝ)) (Nat.cast_nonneg n)
            (3 / 2) 4).symm
        _ = (n : ℝ) ^ (6 : ℝ) := by norm_num
    rw [mul_pow, hscalePow]
    ring
  change (675 / 2 : ℝ) * |t / σ| ^ 4 *
      BooleanSlices.scale n (27 / 5) ≤
        (5400 / a ^ 4) * q / √(n : ℝ)
  rw [abs_div, abs_of_pos hσ]
  calc
    (675 / 2 : ℝ) * (q / σ) ^ 4 * BooleanSlices.scale n (27 / 5) =
        (675 / 2 : ℝ) *
          (q ^ 4 / σ ^ 4) * BooleanSlices.scale n (27 / 5) := by ring
    _ ≤ (675 / 2 : ℝ) *
          (q ^ 4 / (a / 2 * BooleanSlices.scale n (3 / 2)) ^ 4) *
            BooleanSlices.scale n (27 / 5) := by
      gcongr
      exact BooleanSlices.scale_nonneg n _
    _ = (5400 / a ^ 4) *
          (q ^ 4 * BooleanSlices.scale n (27 / 5) /
            BooleanSlices.scale n 6) := by
      rw [hdenom]
      field_simp [ha.ne', hscale6.ne']
      ring
    _ ≤ (5400 / a ^ 4) * (q / √(n : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (5400 / a ^ 4) * q / √(n : ℝ) := by ring

lemma gaussian_graph_terms_le_sqrt_scale {n : ℕ}
    (G : SimpleGraph (Fin n)) (σ a t : ℝ)
    (hn : 1 ≤ n) (ha : 0 < a) (hσ : 0 < σ)
    (hσLower : (a / 2) * BooleanSlices.scale n (3 / 2) ≤ σ)
    (ht : |t| ≤ √(n : ℝ)) :
    |t / σ| * √((G.edgeFinset.card : ℝ) / 16) +
        t ^ 2 * (G.edgeFinset.card : ℝ) / (32 * σ ^ 2) ≤
      (1 / (2 * a) + 1 / (8 * a ^ 2)) * |t| / √(n : ℝ) := by
  let q := |t|
  let N : ℝ := n
  let r := √N
  let E : ℝ := G.edgeFinset.card
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast hnPos
  have hr : 0 < r := Real.sqrt_pos.2 hN
  have hq : 0 ≤ q := abs_nonneg t
  have hE : 0 ≤ E := by positivity
  have hedge : E ≤ N ^ 2 := edgeFinset_card_cast_le_sq G
  have hsqrtEdge : √(E / 16) ≤ N / 4 :=
    sqrt_edge_card_div_sixteen_le G
  have hscale : BooleanSlices.scale n (3 / 2) = N * r :=
    scale_three_halves_eq_mul_sqrt hnPos
  have hσLower' : a / 2 * (N * r) ≤ σ := by simpa [hscale] using hσLower
  have hfirstCore : N / (4 * σ) ≤ 1 / (2 * a * r) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hσ)
      (mul_pos (mul_pos (by norm_num) ha) hr)]
    nlinarith
  have hfirst : |t / σ| * √(E / 16) ≤ (1 / (2 * a)) * q / r := by
    rw [abs_div, abs_of_pos hσ]
    calc
      q / σ * √(E / 16) ≤ q / σ * (N / 4) := by
        gcongr
      _ = q * (N / (4 * σ)) := by ring
      _ ≤ q * (1 / (2 * a * r)) :=
        mul_le_mul_of_nonneg_left hfirstCore hq
      _ = (1 / (2 * a)) * q / r := by ring
  have hσsqRaw := pow_le_pow_left₀
    (mul_nonneg (div_nonneg ha.le (by norm_num))
      (BooleanSlices.scale_nonneg n _)) hσLower 2
  have hscaleSq : BooleanSlices.scale n (3 / 2) ^ 2 = N ^ 3 := by
    dsimp only [BooleanSlices.scale, N]
    exact n_rpow_three_halves_sq n
  have hσsq : a ^ 2 / 4 * N ^ 3 ≤ σ ^ 2 := by
    calc
      a ^ 2 / 4 * N ^ 3 =
          ((a / 2) * BooleanSlices.scale n (3 / 2)) ^ 2 := by
        rw [mul_pow, hscaleSq]
        ring
      _ ≤ σ ^ 2 := hσsqRaw
  have hcross :
      (q ^ 2 * N ^ 2) * (8 * a ^ 2 * N) ≤
        q ^ 2 * (32 * σ ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hσsq
      (by positivity : 0 ≤ 32 * q ^ 2)
    nlinarith
  have hvarCore :
      q ^ 2 * N ^ 2 / (32 * σ ^ 2) ≤ q ^ 2 / (8 * a ^ 2 * N) := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hσ))
      (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos ha)) hN)]
    exact hcross
  have hqRatio : q / r ≤ 1 := (div_le_one hr).2 ht
  have hqRatioNonneg : 0 ≤ q / r := div_nonneg hq hr.le
  have hfreq : q ^ 2 / N ≤ q / r := by
    calc
      q ^ 2 / N = (q / r) ^ 2 := by
        rw [show N = r ^ 2 by
          dsimp only [r]
          exact (Real.sq_sqrt hN.le).symm]
        field_simp [hr.ne']
      _ ≤ q / r := by nlinarith [sq_nonneg (q / r)]
  have hsecond : t ^ 2 * E / (32 * σ ^ 2) ≤
      (1 / (8 * a ^ 2)) * q / r := by
    have htSq : t ^ 2 = q ^ 2 := by
      dsimp only [q]
      exact (sq_abs t).symm
    rw [htSq]
    calc
      q ^ 2 * E / (32 * σ ^ 2) ≤
          q ^ 2 * N ^ 2 / (32 * σ ^ 2) := by
        gcongr
      _ ≤ q ^ 2 / (8 * a ^ 2 * N) := hvarCore
      _ = (1 / (8 * a ^ 2)) * (q ^ 2 / N) := by ring
      _ ≤ (1 / (8 * a ^ 2)) * (q / r) := by
        exact mul_le_mul_of_nonneg_left hfreq (by positivity)
      _ = (1 / (8 * a ^ 2)) * q / r := by ring
  change |t / σ| * √(E / 16) + t ^ 2 * E / (32 * σ ^ 2) ≤
      (1 / (2 * a) + 1 / (8 * a ^ 2)) * q / r
  calc
    |t / σ| * √(E / 16) + t ^ 2 * E / (32 * σ ^ 2) ≤
        (1 / (2 * a)) * q / r + (1 / (8 * a ^ 2)) * q / r :=
      add_le_add hfirst hsecond
    _ = (1 / (2 * a) + 1 / (8 * a ^ 2)) * q / r := by ring

lemma graphSliceLinear_abs_le_scale_one_fifth {n : ℕ}
    (G : SimpleGraph (Fin n)) (c : Fin n → ℝ) (H : ℝ)
    (hn : 1 ≤ n) (hcNonneg : ∀ i, 0 ≤ c i)
    (hcUpper : ∀ i, c i ≤ H * n)
    (hlarge : H / 2 + 1 / 4 ≤ BooleanSlices.scale n (1 / 10)) :
    ∀ i, |graphSliceLinear G c i| ≤
      BooleanSlices.scale n (1 / 2 + 3 * (1 / 5 : ℝ)) := by
  intro i
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hdegNat : G.degree i ≤ n :=
    Nat.le_of_lt (by simpa using G.degree_lt_card_verts i)
  have hdeg : (G.degree i : ℝ) ≤ n := by exact_mod_cast hdegNat
  have hlinNonneg := graphSliceLinear_nonneg G c hcNonneg i
  rw [abs_of_nonneg hlinNonneg]
  calc
    graphSliceLinear G c i = c i / 2 + (G.degree i : ℝ) / 4 := rfl
    _ ≤ (H * n) / 2 + (n : ℝ) / 4 := by
      exact add_le_add
        (div_le_div_of_nonneg_right (hcUpper i) (by norm_num))
        (div_le_div_of_nonneg_right hdeg (by norm_num))
    _ = (H / 2 + 1 / 4) * (n : ℝ) := by ring
    _ ≤ BooleanSlices.scale n (1 / 10) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hlarge hnR
    _ = BooleanSlices.scale n (1 / 2 + 3 * (1 / 5 : ℝ)) := by
      rw [show (n : ℝ) = BooleanSlices.scale n 1 by
        simp [BooleanSlices.scale]]
      rw [mul_comm, BooleanSlices.scale_mul
        (lt_of_lt_of_le (by norm_num) hn)]
      congr 1
      ring

/-- KSSS Lemma 7.1 on an explicit central band.  Positive edge density and
bounded nonnegative perturbations give a normalized characteristic-function
error of order `|t| / √n`; all constants and the eventual coefficient-size
condition are explicit. -/
theorem ksssLemma71_explicit {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (a H : ℝ) (hn : 1 ≤ n) (ha : 0 < a)
    (hcNonneg : ∀ i, 0 ≤ c i) (hcUpper : ∀ i, c i ≤ H * n)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hlarge : H / 2 + 1 / 4 ≤ BooleanSlices.scale n (1 / 10))
    (t : ℝ) (ht : |t| ≤ BooleanSlices.scale n (1 / 30)) :
    ‖Complex.exp (-(((((t / graphPerturbedSigma G e₀ c) *
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) *
          Complex.I))) *
          BooleanSlices.finiteCharacteristic
            (Probability.perturbedEdgePolynomial G e₀ c)
            (t / graphPerturbedSigma G e₀ c) -
        GaussianQuadratic.standardNormalChar t‖ ≤
      (5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)) *
        |t| / √(n : ℝ) := by
  let σ := graphPerturbedSigma G e₀ c
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hσ : 0 < σ :=
    graphPerturbedSigma_pos G e₀ c hnPos ha hcNonneg hedge
  have hσLower : (a / 2) * BooleanSlices.scale n (3 / 2) ≤ σ :=
    graphPerturbedSigma_lower G e₀ c hnPos ha.le hcNonneg hedge
  have hf := graphSliceLinear_abs_le_scale_one_fifth
    G c H hn hcNonneg hcUpper hlarge
  have hbase := norm_centeredGraphCharacteristic_sub_standardNormalChar_le
    G e₀ c (1 / 5) (by norm_num) hn hf hσ t
  have hinv := invariance_scale_bound_one_fifth σ a t hn ha hσ hσLower ht
  have hsqrtScale : √(n : ℝ) = BooleanSlices.scale n (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    rfl
  have htSqrt : |t| ≤ √(n : ℝ) := by
    rw [hsqrtScale]
    exact ht.trans (BooleanSlices.scale_mono_exponent hn (by norm_num))
  have hgauss := gaussian_graph_terms_le_sqrt_scale
    G σ a t hn ha hσ hσLower htSqrt
  change ‖Complex.exp (-(((((t / σ) *
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) *
          Complex.I))) *
          BooleanSlices.finiteCharacteristic
            (Probability.perturbedEdgePolynomial G e₀ c) (t / σ) -
        GaussianQuadratic.standardNormalChar t‖ ≤ _
  calc
    ‖Complex.exp (-(((((t / σ) *
          Probability.expectation (1 / 2 : ℝ)
            (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) *
          Complex.I))) *
          BooleanSlices.finiteCharacteristic
            (Probability.perturbedEdgePolynomial G e₀ c) (t / σ) -
        GaussianQuadratic.standardNormalChar t‖ ≤
      (675 / 2 : ℝ) * |t / σ| ^ 4 *
          BooleanSlices.scale n (27 / 5) +
        (|t / σ| * √((G.edgeFinset.card : ℝ) / 16) +
          t ^ 2 * (G.edgeFinset.card : ℝ) / (32 * σ ^ 2)) := by
      dsimp only [σ] at hinv hgauss ⊢
      convert hbase using 1 <;> ring
    _ ≤ (5400 / a ^ 4) * |t| / √(n : ℝ) +
          (1 / (2 * a) + 1 / (8 * a ^ 2)) * |t| / √(n : ℝ) :=
      add_le_add hinv hgauss
    _ = (5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)) *
        |t| / √(n : ℝ) := by ring

/-- Characteristic function of the centered (but unnormalized) perturbed
induced-edge count. -/
noncomputable def centeredGraphCharacteristic {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℂ :=
  Complex.exp (-(((τ * Probability.expectation (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) * Complex.I)) *
    BooleanSlices.finiteCharacteristic
      (Probability.perturbedEdgePolynomial G e₀ c) τ

/-- Characteristic function of the centered Gaussian having the same
variance as the perturbed induced-edge count. -/
noncomputable def matchingGraphGaussianCharacteristic {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℂ :=
  GaussianQuadratic.standardNormalChar (graphPerturbedSigma G e₀ c * τ)

/-- Raw-frequency form of the explicit Lemma 7.1 estimate. -/
theorem ksssLemma71_raw_explicit {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (a H : ℝ) (hn : 1 ≤ n) (ha : 0 < a)
    (hcNonneg : ∀ i, 0 ≤ c i) (hcUpper : ∀ i, c i ≤ H * n)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hlarge : H / 2 + 1 / 4 ≤ BooleanSlices.scale n (1 / 10))
    (τ : ℝ)
    (hτ : |graphPerturbedSigma G e₀ c * τ| ≤
      BooleanSlices.scale n (1 / 30)) :
    ‖centeredGraphCharacteristic G e₀ c τ -
        matchingGraphGaussianCharacteristic G e₀ c τ‖ ≤
      (5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)) *
        graphPerturbedSigma G e₀ c * |τ| / √(n : ℝ) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hσ := graphPerturbedSigma_pos G e₀ c hnPos ha hcNonneg hedge
  have h := ksssLemma71_explicit G e₀ c a H hn ha hcNonneg hcUpper
    hedge hlarge (graphPerturbedSigma G e₀ c * τ) hτ
  unfold centeredGraphCharacteristic matchingGraphGaussianCharacteristic
  convert h using 1 <;> field_simp [hσ.ne'] <;>
    simp only [abs_mul, abs_of_pos hσ] <;> ring

/-- Raw-frequency Lemma 7.1 on the central band used by the unstructured
Fourier decomposition.  The source later takes `2 * γ = 1 / 5000`, well
inside the normalized range `n^(1/30)`. -/
theorem ksssLemma71_linearBand_explicit {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (a H γ : ℝ) (hn : 1 ≤ n) (ha : 0 < a)
    (hcNonneg : ∀ i, 0 ≤ c i) (hcUpper : ∀ i, c i ≤ H * n)
    (hedge : a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
    (hlarge : H / 2 + 1 / 4 ≤ BooleanSlices.scale n (1 / 10))
    (hγ : 2 * γ ≤ 1 / 30) (τ : ℝ)
    (hτ : |τ| ≤ BooleanSlices.scale n (2 * γ) /
      graphPerturbedSigma G e₀ c) :
    ‖centeredGraphCharacteristic G e₀ c τ -
        matchingGraphGaussianCharacteristic G e₀ c τ‖ ≤
      (5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)) *
        graphPerturbedSigma G e₀ c * |τ| / √(n : ℝ) := by
  have hnPos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hσ := graphPerturbedSigma_pos G e₀ c hnPos ha hcNonneg hedge
  have hscale : BooleanSlices.scale n (2 * γ) ≤
      BooleanSlices.scale n (1 / 30) :=
    BooleanSlices.scale_mono_exponent hn hγ
  apply ksssLemma71_raw_explicit G e₀ c a H hn ha hcNonneg hcUpper
    hedge hlarge τ
  calc
    |graphPerturbedSigma G e₀ c * τ| =
        graphPerturbedSigma G e₀ c * |τ| := by
      rw [abs_mul, abs_of_pos hσ]
    _ ≤ graphPerturbedSigma G e₀ c *
          (BooleanSlices.scale n (2 * γ) /
            graphPerturbedSigma G e₀ c) :=
      mul_le_mul_of_nonneg_left hτ hσ.le
    _ = BooleanSlices.scale n (2 * γ) := by
      field_simp
    _ ≤ BooleanSlices.scale n (1 / 30) := hscale

/-- Eventual, source-shaped statement of KSSS Lemma 7.1. -/
def KSSSLemma71 : Prop :=
  ∀ a H : ℝ, 0 < a → 0 ≤ H →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ),
          (∀ i, 0 ≤ c i ∧ c i ≤ H * n) →
          a * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) →
          ∀ t : ℝ, |t| ≤ BooleanSlices.scale n (1 / 30) →
            ‖Complex.exp (-(((((t / graphPerturbedSigma G e₀ c) *
                  Probability.expectation (1 / 2 : ℝ)
                    (Probability.perturbedEdgePolynomial G e₀ c) : ℝ) : ℂ) *
                  Complex.I))) *
                  BooleanSlices.finiteCharacteristic
                    (Probability.perturbedEdgePolynomial G e₀ c)
                    (t / graphPerturbedSigma G e₀ c) -
                GaussianQuadratic.standardNormalChar t‖ ≤
              C * |t| / √(n : ℝ)

theorem ksssLemma71 : KSSSLemma71 := by
  intro a H ha hH
  let C := 5400 / a ^ 4 + 1 / (2 * a) + 1 / (8 * a ^ 2)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  have hlarge := BooleanSlices.eventually_const_le_scale
    (H / 2 + 1 / 4) (1 / 10) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1, hlarge] with n hn hlargeN
  intro G e₀ c hc hedge t ht
  exact ksssLemma71_explicit G e₀ c a H hn ha
    (fun i ↦ (hc i).1) (fun i ↦ (hc i).2) hedge hlargeN t ht

end GraphQuadratic
end Erdos88
