import Wikipedia.NoExoticSixSphere.OrthogonalPolygonDifferential
import Wikipedia.NoExoticSixSphere.OrthogonalVertexVariationDerivative

/-!
# An explicit local descent family for polygon energy

Move every vertex by the exponential of minus its velocity jump. The actual
energy derivative is a continuous pairing involving the current jumps and
the initial direction. At time zero it is minus twice the sum of squared
Hilbert--Schmidt jump norms, and is strictly negative off the critical locus.
-/

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalExponential OrthogonalVertexSpace
  HilbertSchmidt

variable {n m : ℕ}

theorem contMDiffOn_velocityJump (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) :
    ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, Model n m) ∞ (velocityJump a b τ) (admissible a b m) := by
  apply contMDiffOn_pi_space.mpr
  intro j
  have hvel (i : Fin (m + 1)) :
      ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, SkewOperators n) ∞
        (fun v ↦ edgeVelocity a b τ v i) (admissible a b m) := by
    have hc : ContMDiffOn 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) ∞
        (fun _ : Space n m ↦ 1 / (τ i.succ - τ i.castSucc)) (admissible a b m) :=
      contMDiffOn_const
    exact hc.smul (contMDiffOn_generator a b i)
  exact (hvel j.castSucc).sub (hvel j.succ)

theorem continuousAt_velocityJump (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) : ContinuousAt (velocityJump a b τ) v :=
  (contMDiffOn_velocityJump a b τ).continuousOn.continuousAt ((isOpen_admissible a b m).mem_nhds hv)

noncomputable def jumpSquareNorm (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : ℝ :=
  ∑ j : Fin m, squareNorm (velocityJump a b τ v j : Vector n →L[ℝ] Vector n)

theorem jumpSquareNorm_nonneg (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    0 ≤ jumpSquareNorm a b τ v := Finset.sum_nonneg (fun _ _ ↦ squareNorm_nonneg _)

theorem jumpSquareNorm_eq_zero_iff (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : jumpSquareNorm a b τ v = 0 ↔ velocityJump a b τ v = 0 := by
  constructor
  · intro h
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) ↦
        squareNorm_nonneg (velocityJump a b τ v j : Vector n →L[ℝ] Vector n))).mp h
    funext j
    exact Subtype.ext ((squareNorm_eq_zero_iff _).mp (he j (Finset.mem_univ j)))
  · intro h
    simp [jumpSquareNorm, h, squareNorm, innerForm]

theorem jumpSquareNorm_pos_of_noncritical (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    0 < jumpSquareNorm a b τ v := by
  apply lt_of_le_of_ne (jumpSquareNorm_nonneg a b τ v)
  intro h
  exact hcrit ((mfderiv_energy_eq_zero_iff a b τ v hv).mpr
    ((jumpSquareNorm_eq_zero_iff a b τ v).mp h.symm))

noncomputable def descent (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) : Space n m := vertexVariation p.1 (-velocityJump a b τ p.1) p.2

theorem descent_zero (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    descent a b τ (v, 0) = v := vertexVariation_zero v _

theorem continuousAt_descent (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible a b m) : ContinuousAt (descent a b τ) p := by
  apply continuousAt_pi.mpr
  intro i
  have hj : ContinuousAt (fun q : Space n m × ℝ ↦ velocityJump a b τ q.1 i) p :=
    (continuous_apply i).continuousAt.comp
      ((continuousAt_velocityJump a b τ hp).comp continuousAt_fst)
  have hs : ContinuousAt (fun q : Space n m × ℝ ↦ q.2 • (-velocityJump a b τ q.1 i)) p :=
    continuousAt_snd.smul hj.neg
  exact ((continuous_apply i).continuousAt.comp continuousAt_fst).mul
    (contMDiff_exp.continuous.continuousAt.comp hs)

noncomputable def descentRate (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) : ℝ :=
  2 * ∑ j : Fin m,
    innerForm (velocityJump a b τ (descent a b τ p) j : Vector n →L[ℝ] Vector n)
      ((-velocityJump a b τ p.1) j : Vector n →L[ℝ] Vector n)

theorem hasDerivAt_descent_energy (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (s : ℝ) (hs : descent a b τ (v, s) ∈ admissible a b m) :
    HasDerivAt (fun t ↦ energy a b τ (descent a b τ (v, t))) (descentRate a b τ (v, s)) s :=
  hasDerivAt_energy_vertexVariation_at a b τ v (-velocityJump a b τ v) s hs

theorem descentRate_zero (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    descentRate a b τ (v, 0) = -2 * jumpSquareNorm a b τ v := by
  have hneg (A : Vector n →L[ℝ] Vector n) : innerForm A (-A) = -squareNorm A := by
    rw [← neg_one_smul ℝ A, innerForm_smul_right]
    simp only [neg_one_mul, squareNorm]
  simp only [descentRate, descent_zero, Pi.neg_apply, Submodule.coe_neg, hneg,
    Finset.sum_neg_distrib, jumpSquareNorm]
  ring

theorem continuousAt_skew_pairing {X : Type*} [TopologicalSpace X] {x : X}
    {F G : X → SkewOperators n} (hF : ContinuousAt F x) (hG : ContinuousAt G x) :
    ContinuousAt (fun y ↦ innerForm (F y : Vector n →L[ℝ] Vector n)
      (G y : Vector n →L[ℝ] Vector n)) x := by
  have hf : ContinuousAt (fun y ↦ (F y : Vector n →L[ℝ] Vector n)) x :=
    continuous_subtype_val.continuousAt.comp hF
  have hg : ContinuousAt (fun y ↦ (G y : Vector n →L[ℝ] Vector n)) x :=
    continuous_subtype_val.continuousAt.comp hG
  apply tendsto_finsetSum
  intro i _
  exact (hf.clm_apply continuousAt_const).inner (hg.clm_apply continuousAt_const)

theorem continuousAt_descentRate (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible a b m)
    (hd : descent a b τ p ∈ admissible a b m) : ContinuousAt (descentRate a b τ) p := by
  have hleft : ContinuousAt (fun q ↦ velocityJump a b τ (descent a b τ q)) p :=
    (continuousAt_velocityJump a b τ hd).comp (continuousAt_descent a b τ hp)
  have hright : ContinuousAt (fun q : Space n m × ℝ ↦ -velocityJump a b τ q.1) p :=
    ((continuousAt_velocityJump a b τ hp).comp continuousAt_fst).neg
  have hterm (j : Fin m) : ContinuousAt (fun q : Space n m × ℝ ↦
      innerForm (velocityJump a b τ (descent a b τ q) j : Vector n →L[ℝ] Vector n)
        ((-velocityJump a b τ q.1) j : Vector n →L[ℝ] Vector n)) p :=
    continuousAt_skew_pairing ((continuous_apply j).continuousAt.comp hleft)
      ((continuous_apply j).continuousAt.comp hright)
  exact continuousAt_const.mul (tendsto_finsetSum Finset.univ (fun j _ ↦ hterm j))

theorem continuousAt_jumpSquareNorm (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible a b m) : ContinuousAt (jumpSquareNorm a b τ) v := by
  have hj := continuousAt_velocityJump a b τ hv
  apply tendsto_finsetSum
  intro j _
  have hcoord : ContinuousAt (fun w ↦ velocityJump a b τ w j) v :=
    (continuous_apply j).continuousAt.comp hj
  exact continuousAt_skew_pairing hcoord hcoord

end NoExoticSixSphere.OrthogonalPolygon
