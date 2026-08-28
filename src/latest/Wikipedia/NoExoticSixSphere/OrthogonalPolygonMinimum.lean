import Wikipedia.NoExoticSixSphere.OrthogonalPolygonSublevels
import Wikipedia.NoExoticSixSphere.OrthogonalStationaryPolygon
import Wikipedia.NoExoticSixSphere.SkewAntipodalMinimum
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.Compact

/-!
# Stationary minimizers in compact polygon sublevels

A minimum on a nonempty compact sublevel is a minimum throughout the
admissible domain: points outside the sublevel have larger energy. Since
the domain is open, this is a local minimum on the actual vertex manifold.
The established first-variation and exponential classification then apply.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization CayleyTransform OrthogonalVertexSpace OrthogonalExponential

variable {n m : ℕ}

theorem isStationary_of_isLocalMin (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hmin : IsLocalMin (energy a b τ) v) : IsStationary a b τ v := by
  intro γ hγ hγzero
  have hadm : γ 0 ∈ admissible a b m := by simpa only [hγzero] using hv
  have hE := (contMDiffOn_energy a b τ).contMDiffAt ((isOpen_admissible a b m).mem_nhds hadm)
  have hc : ContDiffAt ℝ ∞ (fun s ↦ energy a b τ (γ s)) 0 :=
    (hE.comp 0 hγ.contMDiffAt).contDiffAt
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  have hm : IsLocalMin (fun s ↦ energy a b τ (γ s)) 0 := by
    rw [← hγzero] at hmin
    exact hmin.comp_continuous hγ.continuous.continuousAt
  have hz := hm.hasDerivAt_eq_zero hd
  simpa only [hz] using hd

theorem exists_stationary_minimizer (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (E : ℝ)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hne : (energySublevel a b τ E).Nonempty) :
    ∃ v ∈ energySublevel a b τ E,
      IsMinOn (energy a b τ) (admissible a b m) v ∧ IsStationary a b τ v := by
  have hcont : ContinuousOn (energy a b τ) (energySublevel a b τ E) :=
    (contMDiffOn_energy a b τ).continuousOn.mono (fun _ hv ↦ hv.1)
  obtain ⟨v, hv, hmin⟩ := hcompact.exists_isMinOn hne hcont
  have hglobal : IsMinOn (energy a b τ) (admissible a b m) v := by
    intro w hw
    by_cases he : energy a b τ w ≤ E
    · exact hmin ⟨hw, he⟩
    · exact hv.2.trans (lt_of_not_ge he).le
  exact ⟨v, hv, hglobal, isStationary_of_isLocalMin a b τ v hv.1
    (hglobal.isLocalMin ((isOpen_admissible a b m).mem_nhds hv.1))⟩

theorem stationary_antipodal_energy_ge (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n)) :
    (n : ℝ) * Real.pi ^ 2 ≤ energy a b τ v := by
  obtain ⟨K, hend, hpath⟩ := stationary_is_exponential a b τ hτ v hv hstat
  simp only [hzero, hone, sub_zero, one_smul] at hend hpath
  have hexpeq : exp K = a⁻¹ * b := by rw [← hend, inv_mul_cancel_left]
  have hexp : (exp K).1.1 = -(1 : Vector n →L[ℝ] Vector n) := by rwa [hexpeq]
  have he := path_energy_eq a b τ hτ hv
  rw [hzero, hone] at he
  have hcompare : OrthogonalPathEnergy.energy (fun t ↦ (path a b τ v t).1.1) 0 1 =
      OrthogonalPathEnergy.energy (fun t ↦ (a * exp (t • K)).1.1) 0 1 :=
    OrthogonalPathEnergy.energy_congr_Icc zero_le_one
      (fun t ht ↦ congrArg (fun q : OrthogonalOperators n ↦ q.1.1) (hpath t ht))
  have hs : energy a b τ v = HilbertSchmidt.squareNorm (K : Vector n →L[ℝ] Vector n) := by
    rw [OrthogonalPathEnergy.energy_left_exp] at hcompare
    simpa only [sub_zero, one_mul] using he.symm.trans hcompare
  rw [hs]
  exact SkewAntipodalSpectrum.squareNorm_ge K hexp

/-- The antipodal lower bound holds for the actual nonsmooth polygon
realizations, by compact minimization rather than an assumed smoothing step. -/
theorem antipodal_energy_ge_of_compact_sublevel (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1) (E : ℝ)
    (hcompact : IsCompact (energySublevel a b τ E))
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (v : Space n m) (hv : v ∈ energySublevel a b τ E) :
    (n : ℝ) * Real.pi ^ 2 ≤ energy a b τ v := by
  obtain ⟨w, hw, hmin, hstat⟩ := exists_stationary_minimizer a b τ E hcompact ⟨v, hv⟩
  exact (stationary_antipodal_energy_ge a b τ hτ hzero hone w hw.1 hstat hanti).trans
    (hmin hv.1)

end NoExoticSixSphere.OrthogonalPolygon
