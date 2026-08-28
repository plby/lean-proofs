import Wikipedia.HopfProblem.OrbitPairSphereVertexVariation

/-!
# First variation of the actual finite sphere polygon energy

Each edge contributes its two logarithm vectors, divided by its time
increment. Summation groups these contributions at the interior vertices.
The resulting tangent balance is the negative half-gradient under the
product of the original round metrics. Zero-length edges are included.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SpherePairedGeodesic SphereAngle

variable {n m : ℕ}

def outgoingLog (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) : Vector (n + 1) :=
  (1 / (τ i.succ - τ i.castSucc)) •
    logVector (vertices a b v i.castSucc).val (vertices a b v i.succ).val

def incomingLog (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (i : Fin (m + 1)) : Vector (n + 1) :=
  (1 / (τ i.succ - τ i.castSucc)) •
    logVector (vertices a b v i.succ).val (vertices a b v i.castSucc).val

def balance (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (j : Fin m) : Vector (n + 1) :=
  incomingLog a b τ v j.castSucc + outgoingLog a b τ v j.succ

theorem inner_balance (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (j : Fin m) : inner ℝ (v j).val (balance a b τ v j) = 0 := by
  have he : vertices a b v j.succ.castSucc = v j := by
    simpa only [Fin.succ_castSucc] using vertices_interior a b v j
  simp only [balance, incomingLog, outgoingLog, he,
    vertices_interior, inner_add_right, real_inner_smul_right,
    inner_logVector (ClosedHemisphere.unit_norm (v j)), mul_zero, add_zero]

def balanceField (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (v : Space n m) : Field v :=
  fun j => ⟨balance a b τ v j,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_balance a b τ v j)⟩

theorem sum_endpoint_pairings {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (O L : Fin (m + 1) → E) (W : Fin (m + 2) → E)
    (hzero : W 0 = 0) (hlast : W (Fin.last (m + 1)) = 0) :
    (∑ i : Fin (m + 1),
      (inner ℝ (W i.castSucc) (O i) + inner ℝ (W i.succ) (L i))) =
      ∑ j : Fin m, inner ℝ (W j.castSucc.succ) (L j.castSucc + O j.succ) := by
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun i => inner ℝ (W i.castSucc) (O i)),
    Fin.sum_univ_castSucc (fun i => inner ℝ (W i.succ) (L i))]
  simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero,
    hlast, hzero, inner_zero_left, add_zero, zero_add,
    inner_add_right, Finset.sum_add_distrib]
  ring

theorem sum_variation_edges (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (W : Field v) :
    (∑ i : Fin (m + 1),
      (-2 * (inner ℝ (vertexField v W i.castSucc)
          (logVector (vertices a b v i.castSucc).val (vertices a b v i.succ).val) +
        inner ℝ (vertexField v W i.succ)
          (logVector (vertices a b v i.succ).val (vertices a b v i.castSucc).val))) /
        (τ i.succ - τ i.castSucc)) =
      -2 * ∑ j : Fin m, inner ℝ (W j : Vector (n + 1)) (balance a b τ v j) := by
  calc
    _ = -2 * ∑ i : Fin (m + 1),
        (inner ℝ (vertexField v W i.castSucc) (outgoingLog a b τ v i) +
          inner ℝ (vertexField v W i.succ) (incomingLog a b τ v i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [outgoingLog, incomingLog, real_inner_smul_right]
      ring
    _ = _ := by
      congr 1
      simpa only [vertexField_interior, balance] using
        sum_endpoint_pairings (outgoingLog a b τ v) (incomingLog a b τ v)
          (vertexField v W) (vertexField_zero v W) (vertexField_last v W)

theorem hasDerivAt_energy_variation_edges (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) (W : Field v) :
    HasDerivAt (fun r => energy a b τ (variation v W r))
      (∑ i : Fin (m + 1),
        (-2 * (inner ℝ (vertexField v W i.castSucc)
            (logVector (vertices a b v i.castSucc).val (vertices a b v i.succ).val) +
          inner ℝ (vertexField v W i.succ)
            (logVector (vertices a b v i.succ).val (vertices a b v i.castSucc).val))) /
          (τ i.succ - τ i.castSucc)) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  have hmem : (vertices a b (variation v W 0) i.castSucc,
      vertices a b (variation v W 0) i.succ) ∈ nonantipodal n := by
    rw [variation_zero]
    exact hv i
  have hd := SphereAngle.hasDerivAt_sphereCost
    (contMDiff_vertices_variation a b v W i.castSucc).contMDiffAt
    (contMDiff_vertices_variation a b v W i.succ).contMDiffAt
    (hasDerivAt_vertices_variation a b v W i.castSucc)
    (hasDerivAt_vertices_variation a b v W i.succ) hmem
  simpa only [variation_zero, edge] using hd.div_const (τ i.succ - τ i.castSucc)

theorem hasDerivAt_energy_variation (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) (W : Field v) :
    HasDerivAt (fun r => energy a b τ (variation v W r))
      (-2 * ∑ j : Fin m, inner ℝ (W j : Vector (n + 1)) (balance a b τ v j)) 0 := by
  rw [← sum_variation_edges]
  exact hasDerivAt_energy_variation_edges a b τ v hv W

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
