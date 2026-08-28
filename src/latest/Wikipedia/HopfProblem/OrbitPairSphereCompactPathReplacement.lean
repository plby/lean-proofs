import Wikipedia.HopfProblem.OrbitPairSphereUniformPathSampling
import Wikipedia.HopfProblem.OrbitPairSphereNearbyHomotopy
import Wikipedia.HopfProblem.OrbitPairSphereStationaryRealization

/-!
# Compact continuous sphere-path families admit bounded-energy polygon replacements

Uniform metric subdivision and normalized interpolation give actual path
homotopies, fixed at both endpoints and on every protected minimum semicircle.
Only the finite polygon family is assigned an energy bound. No finite energy
is assumed for the original continuous paths. Refinement to a later prescribed
energy mesh remains a separate step.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereSemicircle UniformTimePartition

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem uniform_minimum_mesh_of_pos (m : ℕ) (hm : 0 < m) :
    ∀ i : Fin (m + 1), Real.pi ^ 2 * (time m i.succ - time m i.castSucc) < Real.pi ^ 2 := by
  intro i
  rw [time_step]
  have hmreal : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hstep : 1 / ((m : ℝ) + 1) < 1 :=
    (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr (by linarith)
  simpa only [mul_one] using mul_lt_mul_of_pos_left hstep (sq_pos_of_pos Real.pi_pos)

variable (H : C(I × X, Sphere n)) (a b : Sphere n) (m : ℕ)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)
    (hanti : b.val = -a.val) (hm : 0 < m)
    (hsmall : ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        dist (H (u, x)).val (H (unitTime m i.castSucc, x)).val < (1 : ℝ) / 4)

include ha hb hanti hm hsmall in
theorem uniformReplacement_fixed_semicircle (x : X) (y : Direction a)
    (hy : ∀ u : I, (H (u, x)).val = SphereGreatCircle.curve a.val y.val Real.pi u)
    (t : I) :
    realizedFamily a b (time m) (strictMono_time m) (sampleUniform H m)
      (sampleUniform_admissible H a b m ha hb hsmall) (t, x) = H (t, x) := by
  have hsample : sampleUniform H m x = semicircleVertices a (time m) y := by
    funext j
    apply Subtype.ext
    exact hy (unitTime m j.castSucc.succ)
  apply Subtype.ext
  change ambientPath a b (time m) (sampleUniform H m x) (t : ℝ) = (H (t, x)).val
  rw [hsample]
  have hpath := path_semicircleVertices a b (time m) (strictMono_time m)
    (time_zero m) (time_last m) hanti (uniform_minimum_mesh_of_pos m hm) ⟨0, hm⟩ y t.2
  exact hpath.trans (hy t).symm

include ha hb hanti hm hsmall in
def uniformReplacementHomotopy (S : Set X)
    (hS : ∀ x ∈ S, ∃ y : Direction a, ∀ u : I,
      (H (u, x)).val = SphereGreatCircle.curve a.val y.val Real.pi u) :
    H.HomotopyRel
      (realizedFamily a b (time m) (strictMono_time m) (sampleUniform H m)
        (sampleUniform_admissible H a b m ha hb hsmall))
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ S} := by
  apply SpherePathHomotopy.nearbyHomotopyRel H _
    (uniformReplacement_close H a b m ha hb hsmall) _
  rintro ⟨t, x⟩ (ht | ht | hx)
  · change t = 0 at ht
    subst t
    exact (realizedFamily_zero a b (time m) (strictMono_time m) (time_zero m)
      (sampleUniform H m) (sampleUniform_admissible H a b m ha hb hsmall) x).trans (ha x).symm
  · change t = 1 at ht
    subst t
    exact (realizedFamily_one a b (time m) (strictMono_time m) (time_last m)
      (sampleUniform H m) (sampleUniform_admissible H a b m ha hb hsmall) x).trans (hb x).symm
  · obtain ⟨y, hy⟩ := hS x hx
    exact uniformReplacement_fixed_semicircle H a b m ha hb hanti hm hsmall x y hy t

theorem exists_bounded_polygon_replacement_fixing_minima [CompactSpace X]
    (H : C(I × X, Sphere n)) (a b : Sphere n)
    (ha : ∀ x, H (0, x) = a) (hb : ∀ x, H (1, x) = b)
    (hanti : b.val = -a.val) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < m ∧ ∃ p : C(X, Space n m),
      ∃ hp : ∀ x, p x ∈ admissible (costDomain n) a b m,
      ∃ E : ℝ, 0 ≤ E ∧ (∀ x, energy a b (time m) (p x) ≤ E) ∧
        Nonempty (H.HomotopyRel (realizedFamily a b (time m) (strictMono_time m) p hp)
          {z | z.1 = 0 ∨ z.1 = 1 ∨ ∃ y : Direction a,
            ∀ u : I, (H (u, z.2)).val = SphereGreatCircle.curve a.val y.val Real.pi u}) := by
  obtain ⟨m, hNm, hsmall⟩ := UniformMetricPartition.exists_uniform_partition H
    (ε := (1 : ℝ) / 4) (by norm_num) (max N 1)
  have hm : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right N 1).trans hNm)
  let p := sampleUniform H m
  have hp : ∀ x, p x ∈ admissible (costDomain n) a b m :=
    sampleUniform_admissible H a b m ha hb hsmall
  obtain ⟨E, hE0, hE⟩ := exists_family_energy_bound a b (time m) p
  refine ⟨m, (le_max_left N 1).trans hNm, hm, p, hp, E, hE0, hE, ⟨?_⟩⟩
  exact uniformReplacementHomotopy H a b m ha hb hanti hm hsmall
    {x | ∃ y : Direction a, ∀ u : I,
      (H (u, x)).val = SphereGreatCircle.curve a.val y.val Real.pi u} (fun _ hx => hx)

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
