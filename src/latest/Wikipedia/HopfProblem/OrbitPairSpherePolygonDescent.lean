import Wikipedia.HopfProblem.OrbitPairSphereLogContinuity
import Wikipedia.HopfProblem.OrbitPairSpherePolygonDifferential
import Wikipedia.HopfProblem.OrbitPairSphereNormalizationDerivative

/-!
# Actual normalized descent for sphere polygon energy

Move each vertex along its initial tangent balance and normalize. The
initial derivative of energy is minus twice the squared balance norm,
strictly negative away from the actual critical locus. Both the motion
and its actual energy derivative depend continuously on the initial
polygon and time wherever the relevant polygons are nonantipodal.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereNormalVariation

variable {n m : ℕ}

def descent (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (p : Space n m × ℝ) : Space n m :=
  normalVariation p.1 (balanceField a b τ p.1) p.2

theorem descent_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    descent a b τ (v, 0) = v := normalVariation_zero v _

def descentAffine (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) (j : Fin m) : Vector (n + 1) :=
  (p.1 j).val + p.2 • balance a b τ p.1 j

theorem descentAffine_ne_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) (j : Fin m) : descentAffine a b τ p j ≠ 0 :=
  affineField_ne_zero p.1 (p.2 • balanceField a b τ p.1) j

theorem descent_val (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) (j : Fin m) :
    (descent a b τ p j).val = NormedSpace.normalize (descentAffine a b τ p j) := rfl

def descentVelocity (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (p : Space n m × ℝ) (j : Fin m) : Vector (n + 1) :=
  normalizeVelocity (descentAffine a b τ p j) (balance a b τ p.1 j)

theorem descentVelocity_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (j : Fin m) : descentVelocity a b τ (v, 0) j = balance a b τ v j := by
  simp only [descentVelocity, descentAffine, zero_smul, add_zero]
  exact normalizeVelocity_of_unit_orthogonal (ClosedHemisphere.unit_norm (v j))
    (inner_balance a b τ v j)

theorem continuousAt_balance_eval_fst (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible (costDomain n) a b m) (j : Fin m) :
    ContinuousAt (fun q : Space n m × ℝ => balance a b τ q.1 j) p := by
  have hb : ContinuousAt (fun q : Space n m × ℝ => balance a b τ q.1) p :=
    ContinuousAt.comp (g := balance a b τ) (f := Prod.fst)
      (continuousAt_balance a b τ hp) continuousAt_fst
  exact ContinuousAt.comp (g := fun W : Fin m → Vector (n + 1) => W j)
    (f := fun q : Space n m × ℝ => balance a b τ q.1)
    (continuous_apply j).continuousAt hb

theorem continuousAt_descentAffine (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible (costDomain n) a b m) (j : Fin m) :
    ContinuousAt (fun q : Space n m × ℝ => descentAffine a b τ q j) p := by
  have hx : Continuous (fun q : Space n m × ℝ => (q.1 j).val) :=
    continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst)
  exact hx.continuousAt.add (continuousAt_snd.smul (continuousAt_balance_eval_fst a b τ hp j))

theorem continuousAt_descent (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible (costDomain n) a b m) :
    ContinuousAt (descent a b τ) p := by
  apply continuousAt_pi.mpr
  intro j
  have hA := continuousAt_descentAffine a b τ hp j
  have hc : ContinuousAt (fun q : Space n m × ℝ => NormedSpace.normalize (descentAffine a b τ q j)) p :=
    (hA.norm.inv₀ (norm_ne_zero_iff.mpr (descentAffine_ne_zero a b τ p j))).smul hA
  exact hc.codRestrict (fun q => (descent a b τ q j).property)

theorem continuousAt_descentVelocity (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible (costDomain n) a b m) (j : Fin m) :
    ContinuousAt (fun q : Space n m × ℝ => descentVelocity a b τ q j) p :=
  continuousAt_normalizeVelocity (continuousAt_descentAffine a b τ hp j)
    (continuousAt_balance_eval_fst a b τ hp j) (descentAffine_ne_zero a b τ p j)

def descentRate (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (p : Space n m × ℝ) : ℝ :=
  -2 * ∑ j : Fin m, inner ℝ (descentVelocity a b τ p j) (balance a b τ (descent a b τ p) j)

theorem hasDerivAt_descent_energy (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (s : ℝ) (hs : descent a b τ (v, s) ∈ admissible (costDomain n) a b m) :
    HasDerivAt (fun t => energy a b τ (descent a b τ (v, t))) (descentRate a b τ (v, s)) s :=
  hasDerivAt_energy_normalVariation_at a b τ v (balanceField a b τ v) s hs

theorem descentRate_zero (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) :
    descentRate a b τ (v, 0) = -2 * balanceSquareNorm a b τ v := by
  simp only [descentRate, descent_zero, descentVelocity_zero,
    real_inner_self_eq_norm_sq, balanceSquareNorm]

theorem continuousAt_descentRate (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {p : Space n m × ℝ} (hp : p.1 ∈ admissible (costDomain n) a b m)
    (hd : descent a b τ p ∈ admissible (costDomain n) a b m) :
    ContinuousAt (descentRate a b τ) p := by
  have hb : ContinuousAt (fun q : Space n m × ℝ => balance a b τ (descent a b τ q)) p :=
    ContinuousAt.comp (g := balance a b τ) (f := descent a b τ)
      (continuousAt_balance a b τ hd) (continuousAt_descent a b τ hp)
  have hterm (j : Fin m) : ContinuousAt (fun q : Space n m × ℝ =>
      inner ℝ (descentVelocity a b τ q j) (balance a b τ (descent a b τ q) j)) p :=
    (continuousAt_descentVelocity a b τ hp j).inner
      ((continuous_apply j).continuousAt.comp hb)
  exact continuousAt_const.mul (tendsto_finsetSum Finset.univ (fun j _ => hterm j))

theorem continuousAt_balanceSquareNorm (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    {v : Space n m} (hv : v ∈ admissible (costDomain n) a b m) :
    ContinuousAt (balanceSquareNorm a b τ) v := by
  have hb := continuousAt_balance a b τ hv
  apply tendsto_finsetSum
  intro j _
  exact (((continuous_apply j).continuousAt.comp hb).norm).pow 2

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
