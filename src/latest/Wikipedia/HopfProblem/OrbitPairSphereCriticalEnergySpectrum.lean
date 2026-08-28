import Wikipedia.HopfProblem.OrbitPairSpherePolygonIndex

/-!
# Discrete critical energies for actual antipodal sphere polygons

On a partition of [0,1], each stationary nonantipodal polygon realizes an
actual great circle. Its positive speed is an odd multiple of pi, so its
energy is ((2q+1)pi)^2. These values increase strictly and only finitely many
can lie below a prescribed cap. No realizability of every value on a fixed
partition is asserted.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ}

def criticalLevel (q : ℕ) : ℝ := ((2 * (q : ℝ) + 1) * Real.pi) ^ 2

theorem criticalLevel_zero : criticalLevel 0 = Real.pi ^ 2 := by
  simp only [criticalLevel, Nat.cast_zero, mul_zero, zero_add, one_mul]

theorem strictMono_criticalLevel : StrictMono criticalLevel := by
  intro q r hqr
  have hcast : (q : ℝ) < r := by exact_mod_cast hqr
  have hq : 0 ≤ (2 * (q : ℝ) + 1) * Real.pi := by positivity
  have hr : 0 ≤ (2 * (r : ℝ) + 1) * Real.pi := by positivity
  apply (sq_lt_sq₀ hq hr).mpr
  exact mul_lt_mul_of_pos_right (by linarith) Real.pi_pos

theorem criticalLevel_ge_min (q : ℕ) : Real.pi ^ 2 ≤ criticalLevel q := by
  rw [← criticalLevel_zero]
  exact strictMono_criticalLevel.monotone (Nat.zero_le q)

theorem exists_criticalLevel_above (c : ℝ) : ∃ N : ℕ, c < criticalLevel N := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  obtain ⟨N, hN⟩ := exists_nat_gt (c / Real.pi ^ 2)
  have hlt : c < (N : ℝ) * Real.pi ^ 2 := (div_lt_iff₀ hp).mp hN
  refine ⟨N, hlt.trans_le ?_⟩
  calc
    (N : ℝ) * Real.pi ^ 2 ≤ (2 * (N : ℝ) + 1) ^ 2 * Real.pi ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hp.le
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ = criticalLevel N := by unfold criticalLevel; ring

theorem stationary_energy_eq_criticalLevel (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) (hstat : IsStationary a b τ v) :
    ∃ q : ℕ, energy a b τ v = criticalLevel q := by
  obtain ⟨y, w, hwpos, hy, hxy, hw, hsample⟩ :=
    exists_greatCircle_of_stationary a b τ hτ v hv hstat (endpoints_ne_of_antipodal a b hanti)
  have hend : SphereGreatCircle.curve a.val y w 1 = -a.val := by
    have he := hsample (Fin.last (m + 1))
    simpa only [vertices_last, hzero, hone, sub_zero, hanti] using he.symm
  obtain ⟨k, hk⟩ := SphereAntipodalIndex.odd_speed_of_antipodal
    (ClosedHemisphere.unit_norm a) hxy hend
  have hk0 : 0 ≤ k := by
    by_contra h
    have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith [Real.pi_pos]
  lift k to ℕ using hk0
  simp only [Int.cast_natCast] at hk
  refine ⟨k, ?_⟩
  rw [energy_eq_speed_sq_mul_of_stationary a b τ hτ v hv hstat,
    hzero, hone, sub_zero, mul_one, ← hw, hk]
  rfl

theorem stationary_antipodal_energy_ge (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) (hstat : IsStationary a b τ v) :
    Real.pi ^ 2 ≤ energy a b τ v := by
  obtain ⟨q, hq⟩ := stationary_energy_eq_criticalLevel a b τ hτ hzero hone hanti v hv hstat
  rw [hq]
  exact criticalLevel_ge_min q

theorem critical_energy_eq_criticalLevel (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m)
    (hcrit : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0) :
    ∃ q : ℕ, energy a b τ v = criticalLevel q :=
  stationary_energy_eq_criticalLevel a b τ hτ hzero hone hanti v hv
    (isStationary_of_mfderiv_eq_zero a b τ v hv hcrit)

theorem noncritical_of_energy_mem_gap (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (v : Space n m)
    (hv : v ∈ admissible (costDomain n) a b m) (q : ℕ)
    (hlow : criticalLevel q < energy a b τ v)
    (hhigh : energy a b τ v < criticalLevel (q + 1)) :
    mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0 := by
  intro hcrit
  obtain ⟨r, hr⟩ := critical_energy_eq_criticalLevel a b τ hτ hzero hone hanti v hv hcrit
  rw [hr] at hlow hhigh
  rcases le_or_gt r q with h | h
  · exact (not_lt_of_ge (strictMono_criticalLevel.monotone h)) hlow
  · exact (not_lt_of_ge (strictMono_criticalLevel.monotone (Nat.succ_le_of_lt h))) hhigh

theorem bounded_critical_labels (a b : Sphere n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val) (c : ℝ) :
    ∃ N : ℕ, ∀ v : Space n m, v ∈ admissible (costDomain n) a b m →
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v = 0 →
      energy a b τ v ≤ c → ∃ q < N, energy a b τ v = criticalLevel q := by
  obtain ⟨N, hN⟩ := exists_criticalLevel_above c
  refine ⟨N, fun v hv hcrit hcap => ?_⟩
  obtain ⟨q, hq⟩ := critical_energy_eq_criticalLevel a b τ hτ hzero hone hanti v hv hcrit
  refine ⟨q, ?_, hq⟩
  by_contra h
  have hle := strictMono_criticalLevel.monotone (le_of_not_gt h)
  rw [← hq] at hle
  exact (not_lt_of_ge (hle.trans hcap)) hN

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
