import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonStationarity
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPolygonRealization
import Wikipedia.NoExoticSixSphere.OrthogonalStationaryPolygon
import Wikipedia.NoExoticSixSphere.OrthogonalPolygonDifferential

/-!
# Critical symplectic polygons are single symplectic exponential paths

The first edge velocity is quaternionic. Vanishing of all symplectic
velocity jumps implies vanishing of the orthogonal jumps as well, so the
orthogonal path formula applies with precisely that same quaternionic
generator. No ambient stationarity assumption is imposed.
-/

noncomputable section

open scoped Manifold
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon

open VertexSpace Exponential

variable {n m : ℕ}

theorem stationary_forget (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) :
    NoExoticSixSphere.OrthogonalPolygon.IsStationary a.val b.val τ (forget v) := by
  have hO := admissible_forget a b hv
  apply NoExoticSixSphere.OrthogonalPolygon.isStationary_of_mfderiv_eq_zero
    a.val b.val τ (forget v) hO
  apply (NoExoticSixSphere.OrthogonalPolygon.mfderiv_energy_eq_zero_iff
    a.val b.val τ (forget v) hO).mpr
  funext j
  rw [velocityJump_forget a b τ hv]
  have hz := congrFun (velocityJump_eq_zero_of_stationary a b τ v hv hstat) j
  change velocityJump a b τ v j = 0 at hz
  rw [hz, map_zero]
  rfl

theorem edgeVelocity_eq_first_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    edgeVelocity a b τ v i = edgeVelocity a b τ v 0 := by
  induction i using Fin.inductionOn with
  | zero => rfl
  | succ j ih => exact (adjacent_edgeVelocity_eq_of_stationary a b τ v hv hstat j).symm.trans ih

theorem generator_eq_time_smul_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) (i : Fin (m + 1)) :
    generator a b v i = (τ i.succ - τ i.castSucc) • edgeVelocity a b τ v 0 := by
  have hδ : τ i.succ - τ i.castSucc ≠ 0 :=
    sub_ne_zero.mpr (hτ (show i.castSucc < i.succ by simp)).ne'
  rw [← edgeVelocity_eq_first_of_stationary a b τ v hv hstat i, edgeVelocity, smul_smul]
  simp [hδ]

theorem vertices_eq_exponential_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) (j : Fin (m + 2)) :
    vertices a b v j = a * exp ((τ j - τ 0) • edgeVelocity a b τ v 0) := by
  induction j using Fin.inductionOn with
  | zero => simp only [vertices_zero, sub_self, zero_smul, exp_zero, mul_one]
  | succ i ih =>
    rw [← generator_endpoint a b hv i, ih,
      generator_eq_time_smul_of_stationary a b τ hτ v hv hstat i,
      _root_.mul_assoc, ← exp_add_smul]
    congr 2
    congr 1
    ring

theorem path_eq_exponential_of_stationary (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ (Fin.last (m + 1)))) :
    path a b τ v t = a * exp ((t - τ 0) • edgeVelocity a b τ v 0) := by
  apply Subtype.ext
  rw [path_forget a b τ hv]
  have h := NoExoticSixSphere.OrthogonalPolygon.path_eq_exponential_of_stationary
    a.val b.val τ hτ (forget v) (admissible_forget a b hv)
    (stationary_forget a b τ v hv hstat) ht
  rw [edgeVelocity_forget a b τ hv] at h
  change NoExoticSixSphere.OrthogonalPolygon.path a.val b.val τ (forget v) t =
    a.val * NoExoticSixSphere.OrthogonalExponential.exp
      (toOrthogonalSkew n ((t - τ 0) • edgeVelocity a b τ v 0))
  rw [map_smul]
  exact h

theorem stationary_is_exponential (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m) (hstat : IsStationary a b τ v) :
    ∃ K : SkewSpace n,
      a * exp ((τ (Fin.last (m + 1)) - τ 0) • K) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))), path a b τ v t = a * exp ((t - τ 0) • K) := by
  refine ⟨edgeVelocity a b τ v 0, ?_, fun _ ht =>
    path_eq_exponential_of_stationary a b τ hτ v hv hstat ht⟩
  have h := vertices_eq_exponential_of_stationary a b τ hτ v hv hstat (Fin.last (m + 1))
  rw [vertices_last] at h
  exact h.symm

theorem critical_is_exponential (a b : symplecticSubgroup n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (v : Space n m)
    (hv : v ∈ admissible a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    ∃ K : SkewSpace n,
      a * exp ((τ (Fin.last (m + 1)) - τ 0) • K) = b ∧
      ∀ t ∈ Icc (τ 0) (τ (Fin.last (m + 1))), path a b τ v t = a * exp ((t - τ 0) • K) :=
  stationary_is_exponential a b τ hτ v hv (isStationary_of_mfderiv_eq_zero a b τ v hv hcrit)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Polygon
