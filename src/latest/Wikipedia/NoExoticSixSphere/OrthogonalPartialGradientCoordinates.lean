import Wikipedia.NoExoticSixSphere.OrthogonalNegativeHessianNeighborhood
import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-!
# Smooth partial-gradient coordinates at nonminimal critical polygons

The first coordinate is the actual differential of polygon energy restricted
to an `(n - 2)`-dimensional negative linear family. The second coordinate is
constant along affine translates of that family. The coordinates are a genuine
smooth partial diffeomorphism on an admissible neighborhood, centered at zero.
-/

open Set
open scoped ContDiff Manifold

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

def localAdmissible (a b : OrthogonalOperators n) (v : Space n m) : Set (Model n m) :=
  (atVertices v).symm ⁻¹' admissible a b m

theorem isOpen_localAdmissible (a b : OrthogonalOperators n) (v : Space n m) :
    IsOpen (localAdmissible a b v) :=
  (isOpen_admissible a b m).preimage (contMDiff_atVertices_symm v).continuous

theorem zero_mem_localAdmissible (a b : OrthogonalOperators n) (v : Space n m)
    (hv : v ∈ admissible a b m) : (0 : Model n m) ∈ localAdmissible a b v := by
  change (atVertices v).symm 0 ∈ admissible a b m
  simpa only [atVertices_symm_zero] using hv

theorem contDiffOn_localEnergy (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) : ContDiffOn ℝ ∞ (localEnergy a b τ v) (localAdmissible a b v) := by
  intro z hz
  have he := (contMDiffOn_energy a b τ).contMDiffAt
    ((isOpen_admissible a b m).mem_nhds hz)
  have hs := (contMDiff_atVertices_symm v).contMDiffAt (x := z)
  exact (he.comp z hs).contDiffAt.contDiffWithinAt

theorem exists_partialGradient_coordinates (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] Model n m), d + 2 = n ∧ Function.Injective L ∧
      Nonempty (PartialGradientCoordinates.LocalData (localEnergy a b τ v) L
        (localAdmissible a b v)) := by
  obtain ⟨d, L, hd, hL, c, hc, ε, hε, hball⟩ :=
    exists_uniform_negative_hessian_neighborhood a b τ hτ hzero hone v hv hcrit hanti habove
  have h0ball : (0 : Model n m) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hsub : Metric.ball (0 : Model n m) ε ⊆ localAdmissible a b v :=
    fun z hz ↦ (hball z hz).1
  have hz : fderiv ℝ (localEnergy a b τ v) 0 = 0 := by
    rw [← mfderiv_energy_eq_localEnergy a b τ v hv.1]
    exact hcrit
  have hdata := PartialGradientCoordinates.nonempty_localData_of_bound
    (D := Fin d → ℝ) (E := Model n m) (localEnergy a b τ v) L
    (Metric.ball 0 ε) Metric.isOpen_ball h0ball
    ((contDiffOn_localEnergy a b τ v).mono hsub) hz c hc (fun z hz ↦ (hball z hz).2)
  exact ⟨d, L, hd, hL, hdata.map (fun C ↦ C.mono hsub)⟩

end NoExoticSixSphere.OrthogonalPolygon
