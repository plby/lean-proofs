import Wikipedia.HopfProblem.OrbitPairSpherePolygonHessian
import Wikipedia.NoExoticSixSphere.NegativeFormNeighborhood
import Wikipedia.NoExoticSixSphere.PartialGradientLocalData

/-!
# Actual negative partial-gradient coordinates for critical sphere polygons

Continuity of the true coordinate Hessian extends the negative family to a
uniformly negative family on an admissible coordinate ball. The checked
finite-dimensional inverse-function construction then gives an actual
partial diffeomorphism whose first coordinate is the energy differential
restricted to that family. This supplies local critical-crossing data.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ}

theorem continuousAt_localEnergy_hessian (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m) :
    ContinuousAt (fderiv ℝ (fderiv ℝ (localEnergy a b τ v))) 0 := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ (localEnergy a b τ v)) 0 :=
    (contDiffAt_localEnergy a b τ v hv).fderiv_right (WithTop.coe_le_coe.mpr le_top)
  exact hd.continuousAt_fderiv one_ne_zero

theorem exists_uniform_negative_hessian_neighborhood (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : b.val = -a.val) (habove : Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] Model n m), d + 2 = 2 * n ∧ Function.Injective L ∧
      ∃ c > 0, ∃ ε > 0, ∀ z ∈ Metric.ball (0 : Model n m) ε,
        z ∈ localAdmissible a b v ∧ ∀ w : Fin d → ℝ,
          fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  obtain ⟨d, R, hd, hR, hneg⟩ :=
    exists_negative_hessianFamily_of_critical a b τ hτ hzero hone v hv hcrit hanti habove
  let L : (Fin d → ℝ) →L[ℝ] Model n m := R.toContinuousLinearMap
  obtain ⟨c, hc, hforms⟩ := NegativeFormNeighborhood.exists_uniform_bound
    (D := Fin d → ℝ) (E := Model n m) (localHessian a b τ v) L hneg
  have hnear : ∀ᶠ z in 𝓝 (0 : Model n m), ∀ w : Fin d → ℝ,
      fderiv ℝ (fderiv ℝ (localEnergy a b τ v)) z (L w) (L w) ≤ -c * ‖w‖ ^ 2 :=
    (continuousAt_localEnergy_hessian a b τ v hv).eventually hforms
  have hmem : ∀ᶠ z in 𝓝 (0 : Model n m), z ∈ localAdmissible a b v :=
    (isOpen_localAdmissible a b v).mem_nhds (zero_mem_localAdmissible a b v hv)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hmem.and hnear)
  exact ⟨d, L, hd, hR, c, hc, ε, hε, fun z hz => hball hz⟩

theorem exists_partialGradient_coordinates (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0)
    (hanti : b.val = -a.val) (habove : Real.pi ^ 2 < energy a b τ v) :
    ∃ (d : ℕ) (L : (Fin d → ℝ) →L[ℝ] Model n m), d + 2 = 2 * n ∧ Function.Injective L ∧
      Nonempty (PartialGradientCoordinates.LocalData (localEnergy a b τ v) L
        (localAdmissible a b v)) := by
  obtain ⟨d, L, hd, hL, c, hc, ε, hε, hball⟩ :=
    exists_uniform_negative_hessian_neighborhood a b τ hτ hzero hone v hv hcrit hanti habove
  have h0ball : (0 : Model n m) ∈ Metric.ball 0 ε := Metric.mem_ball_self hε
  have hsub : Metric.ball (0 : Model n m) ε ⊆ localAdmissible a b v :=
    fun z hz => (hball z hz).1
  have hdata := PartialGradientCoordinates.nonempty_localData_of_bound
    (D := Fin d → ℝ) (E := Model n m) (localEnergy a b τ v) L
    (Metric.ball 0 ε) Metric.isOpen_ball h0ball
    ((contDiffOn_localEnergy a b τ v).mono hsub) (localEnergy_critical a b τ v hv hcrit)
    c hc (fun z hz => (hball z hz).2)
  exact ⟨d, L, hd, hL, hdata.map (fun C => C.mono hsub)⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
