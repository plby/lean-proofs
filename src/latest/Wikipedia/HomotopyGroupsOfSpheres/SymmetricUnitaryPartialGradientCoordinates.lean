import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryNegativeHessianNeighborhood
import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-! # Partial-gradient coordinates at constrained antipodal critical polygons -/

open scoped Matrix.Norms.Frobenius ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions NoExoticSixSphere

variable {N : Type*} [Fintype N] [DecidableEq N] {m : ℕ}

def localAdmissible (a b : SpecialSpace N) (v : VertexSpace.Space N m) : Set (Model N m) :=
  (atVertices v).symm ⁻¹' admissible a b m

theorem isOpen_localAdmissible (a b : SpecialSpace N) (v : VertexSpace.Space N m) :
    IsOpen (localAdmissible a b v) :=
  (isOpen_admissible a b m).preimage (continuous_atVertices_symm v)

theorem zero_mem_localAdmissible (a b : SpecialSpace N) (v : VertexSpace.Space N m)
    (hv : v ∈ admissible a b m) : (0 : Model N m) ∈ localAdmissible a b v := by
  change (atVertices v).symm 0 ∈ admissible a b m
  simpa only [atVertices_symm_zero] using hv

theorem exists_partialGradient_coordinates (n : ℕ) (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity (antipode n) τ v) 0 = 0)
    (habove : (4 * n : ℝ) * Real.pi ^ 2 < energy specialIdentity (antipode n) τ v) :
    ∃ L : (Fin n → ℝ) →L[ℝ] Model (Index n) m, Function.Injective L ∧
      Nonempty (PartialGradientCoordinates.LocalData (localEnergy specialIdentity (antipode n) τ v)
        L (localAdmissible specialIdentity (antipode n) v)) := by
  obtain ⟨L, hL, c, hc, ε, hε, hball⟩ :=
    exists_uniform_negative_hessian_neighborhood n τ hτ hzero hone v hv hcrit habove
  have h0ball : (0 : Model (Index n) m) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hsub : Metric.ball (0 : Model (Index n) m) ε ⊆
      localAdmissible specialIdentity (antipode n) v := fun z hz ↦ (hball z hz).1
  have hdata := PartialGradientCoordinates.nonempty_localData_of_bound
    (D := Fin n → ℝ) (E := Model (Index n) m) (localEnergy specialIdentity (antipode n) τ v) L
    (Metric.ball 0 ε) Metric.isOpen_ball h0ball
    ((contDiffOn_localEnergy specialIdentity (antipode n) τ v).mono hsub) hcrit c hc
    (fun z hz ↦ (hball z hz).2)
  exact ⟨L, hL, hdata.map (fun C ↦ C.mono hsub)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
