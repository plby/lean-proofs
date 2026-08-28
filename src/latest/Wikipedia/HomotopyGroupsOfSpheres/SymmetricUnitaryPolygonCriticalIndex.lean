import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonVariationComparison
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySmoothFamilyHessian
import Wikipedia.HomotopyGroupsOfSpheres.BalancedAntipodalNegativeFamily

/-!
# A rank-growing negative Hessian subspace at every nonminimal antipodal critical polygon

The original constrained negative variations are sampled at the vertices.
Their energy contact with the smooth exponential transfers negativity to
the finite energy, and the derivative of the actual chart gives an
injective linear negative subspace of the constrained Hessian.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace RealSymmetricMixing BalancedRealInvolutions

local instance criticalIndexDirectionSelfChart (n : ℕ) :
    LocalLogarithm.NormedChartedSpace (DirectionSpace (Index n)) (DirectionSpace (Index n)) :=
  chartedSpaceSelf _

theorem exists_negative_hessianFamily_of_critical (n : ℕ) {m : ℕ}
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0)
    (habove : (4 * n : ℝ) * Real.pi ^ 2 < energy specialIdentity (antipode n) τ v) :
    ∃ L : (Fin n → ℝ) →ₗ[ℝ] Model (Index n) m, Function.Injective L ∧
      ∀ c, c ≠ 0 → localHessian specialIdentity (antipode n) τ v (L c) (L c) < 0 := by
  obtain ⟨A, hexp, hnot, hpath⟩ := critical_antipodal_generator n τ hτ hzero hone v hv hcrit habove
  have hend : exponential A = antipode n := exponential_eq_antipode n A hexp
  have htime (j : Fin (m + 2)) : τ j ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le j)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last j)
  have hmatch (j : Fin (m + 2)) :
      exponentialCurve A (τ j) = vertices specialIdentity (antipode n) v j :=
    (hpath _ (htime j)).symm.trans (path_vertex specialIdentity (antipode n) τ hτ v hv j)
  have hcontact := exponential_polygon_energy_contact (antipode n) τ hτ hzero hone v hv A hpath
  obtain ⟨T, _, _, hneg⟩ := exists_antipodal_negative_variation_family n A hexp hnot
  let F : (Fin n → ℝ) → VertexSpace.Space (Index n) m :=
    fun c ↦ sampledVariationPoint A τ (T c)
  have hT : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, DirectionSpace (Index n)) ∞ T := by
    simpa only [] using! (finiteLinearMap_contDiff T).contMDiff
  have hF : ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Model (Index n) m) ∞ F :=
    (contMDiff_sampledVariationPoint A τ).comp hT
  have hFzero : F 0 = v := by
    change sampledVariationPoint A τ (T 0) = v
    rw [map_zero]
    have hp := sampledVariationPoint_smul A (0 : DirectionSpace (Index n)) τ 0
    simp only [zero_smul] at hp
    rw [hp]
    exact sampledVariation_zero A 0 (antipode n) τ v hmatch
  apply negative_hessianFamily_of_smooth_family specialIdentity (antipode n)
    τ v hv hcrit F hF hFzero
  intro c hc
  have hle := secondDerivative_sampled_le (antipode n) τ hτ hzero hone v hv
    A (T c) hend hmatch hcontact
  have hstrict := lt_of_le_of_lt hle (hneg c hc)
  simpa only [F, map_smul, sampledVariationPoint_smul] using hstrict

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
