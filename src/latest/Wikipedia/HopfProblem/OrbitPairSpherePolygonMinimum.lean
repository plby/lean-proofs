import Wikipedia.HopfProblem.OrbitPairSphereCriticalEnergySpectrum
import Wikipedia.HopfProblem.OrbitPairSpherePolygonSublevels
import Mathlib.Topology.Order.Compact

/-!
# Compact minimization and the actual minimum sphere polygons

A mesh-controlled closed energy sublevel lies wholly in the smooth domain.
Minimizing its continuous energy gives a genuine stationary polygon, hence
the antipodal lower bound pi^2. Equality forces speed pi in the checked
great-circle classification. Conversely, samples of such a semicircle have
energy pi^2 by the actual path-energy comparison and this lower bound.
No smoothing of a broken path at its corners is assumed.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace

variable {n m : ℕ}

theorem isStationary_of_isLocalMin (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible (costDomain n) a b m)
    (hmin : IsLocalMin (energy a b τ) v) : IsStationary a b τ v := by
  intro γ hγ hγzero
  have hadm : γ 0 ∈ admissible (costDomain n) a b m := by simpa only [hγzero] using hv
  have hE := (contMDiffOn_energy (costDomain n) a b τ).contMDiffAt
    ((isOpen_admissible (costDomain n) a b m).mem_nhds hadm)
  have hc : ContDiffAt ℝ ∞ (fun s => energy a b τ (γ s)) 0 :=
    (ContMDiffAt.comp (g := energy a b τ) (f := γ) 0 hE hγ.contMDiffAt).contDiffAt
  have hd := (hc.differentiableAt (by simp)).hasDerivAt
  have hm : IsLocalMin (fun s => energy a b τ (γ s)) 0 := by
    rw [← hγzero] at hmin
    exact hmin.comp_continuous hγ.continuous.continuousAt
  have hz := hm.hasDerivAt_eq_zero hd
  simpa only [hz] using hd

theorem exists_stationary_minimizer (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (hne : {v : Space n m | energy a b τ v ≤ c}.Nonempty) :
    ∃ v : Space n m, energy a b τ v ≤ c ∧
      IsMinOn (energy a b τ) univ v ∧ IsStationary a b τ v := by
  obtain ⟨v, hv, hmin⟩ := (isCompact_sublevel a b τ c).exists_isMinOn hne
    (continuous_energy a b τ).continuousOn
  have hglobal : IsMinOn (energy a b τ) univ v := by
    intro w _
    by_cases he : energy a b τ w ≤ c
    · exact hmin he
    · exact hv.trans (lt_of_not_ge he).le
  have hadm := sublevel_subset_admissible a b τ hτ c hmesh hv
  exact ⟨v, hv, hglobal, isStationary_of_isLocalMin a b τ v hadm
    (hglobal.isLocalMin Filter.univ_mem)⟩

theorem antipodal_energy_ge_of_mesh (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (v : Space n m) (hv : energy a b τ v ≤ c) : Real.pi ^ 2 ≤ energy a b τ v := by
  obtain ⟨w, hw, hmin, hstat⟩ := exists_stationary_minimizer a b τ hτ c hmesh ⟨v, hv⟩
  have hadm := sublevel_subset_admissible a b τ hτ c hmesh hw
  exact (stationary_antipodal_energy_ge a b τ hτ hzero hone hanti w hadm hstat).trans
    (hmin (mem_univ v))

theorem isStationary_of_minimum_energy (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (v : Space n m) (hv : energy a b τ v ≤ c) (he : energy a b τ v = Real.pi ^ 2) :
    IsStationary a b τ v := by
  have hmin : IsMinOn (energy a b τ) univ v := by
    intro w _
    by_cases hw : energy a b τ w ≤ c
    · rw [he]
      exact antipodal_energy_ge_of_mesh a b τ hτ hzero hone hanti c hmesh w hw
    · exact hv.trans (lt_of_not_ge hw).le
  exact isStationary_of_isLocalMin a b τ v
    (sublevel_subset_admissible a b τ hτ c hmesh hv) (hmin.isLocalMin Filter.univ_mem)

theorem energy_eq_min_iff_greatCircle (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (c : ℝ)
    (hmesh : ∀ i : Fin (m + 1), c * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (v : Space n m) (hv : energy a b τ v ≤ c) :
    energy a b τ v = Real.pi ^ 2 ↔
      ∃ y : Vector (n + 1), ‖y‖ = 1 ∧ inner ℝ a.val y = 0 ∧
        ∀ j : Fin (m + 2), (vertices a b v j).val =
          SphereGreatCircle.curve a.val y Real.pi (τ j) := by
  constructor
  · intro he
    have hadm := sublevel_subset_admissible a b τ hτ c hmesh hv
    have hstat := isStationary_of_minimum_energy a b τ hτ hzero hone hanti c hmesh v hv he
    obtain ⟨y, w, hwpos, hy, hxy, hw, hsample⟩ :=
      exists_greatCircle_of_stationary a b τ hτ v hadm hstat
        (endpoints_ne_of_antipodal a b hanti)
    have hE := energy_eq_speed_sq_mul_of_stationary a b τ hτ v hadm hstat
    rw [hzero, hone, sub_zero, mul_one, ← hw, he] at hE
    have hwpi : w = Real.pi := by nlinarith [Real.pi_pos]
    exact ⟨y, hy, hxy, fun j => by simpa only [hzero, sub_zero, hwpi] using hsample j⟩
  · rintro ⟨y, hy, hxy, hsample⟩
    have hle := energy_le_of_matching_vertices a b τ hτ v
      (SphereGreatCircle.contDiff_curve a.val y Real.pi)
      (SphereGreatCircle.norm_curve (ClosedHemisphere.unit_norm a) hy hxy Real.pi)
      (fun j => (hsample j).symm)
    rw [hzero, hone, SphereGreatCircle.energy_curve (ClosedHemisphere.unit_norm a) hy hxy] at hle
    exact le_antisymm hle (antipodal_energy_ge_of_mesh a b τ hτ hzero hone hanti c hmesh v hv)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
