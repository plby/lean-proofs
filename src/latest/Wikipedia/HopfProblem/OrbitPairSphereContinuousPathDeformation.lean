import Wikipedia.HopfProblem.OrbitPairSphereCompactPathReplacement
import Wikipedia.HopfProblem.OrbitPairSphereUniformRefinement
import Wikipedia.HopfProblem.OrbitPairSphereMinimumPathDeformation

/-!
# Relative deformation of compact continuous sphere-path families to semicircles

Replace the arbitrary continuous paths by polygons, obtain their finite energy
bound, and only then refine to the mesh required by global minimum deformation.
Refinement preserves both the realized path and the energy. Concatenating the
actual homotopies fixes endpoints and every path that was already a semicircle.
No finite-energy, smoothness, or partition hypothesis on the original paths is
assumed. The parameter manifold has the proved negative-index dimension bound.
-/

noncomputable section

open Set Module
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace SphereSemicircle UniformTimePartition

variable {X : Type*} [TopologicalSpace X] {n m : ℕ}

def minimumPathParameters (a : Sphere n) (H : C(unitInterval × X, Sphere n)) : Set X :=
  {x | ∃ y : Direction a, ∀ u : unitInterval,
    (H (u, x)).val = SphereGreatCircle.curve a.val y.val Real.pi u}

theorem minimum_of_realized_semicircle (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (p : C(X, Space n m)) (hp : ∀ x, p x ∈ admissible (costDomain n) a b m)
    (x : X) (y : Direction a)
    (hy : ∀ t : unitInterval, (realizedFamily a b τ hτ p hp (t, x)).val =
      SphereGreatCircle.curve a.val y.val Real.pi t) : p x ∈ minimumSet a b τ := by
  have he : p x = semicircleVertices a τ y := by
    funext j
    apply Subtype.ext
    have ht := interior_time_mem τ hτ hzero hone j
    let t : unitInterval := ⟨τ j.castSucc.succ, ht.1.le, ht.2.le⟩
    have h := hy t
    change (path a b τ hτ ⟨p x, hp x⟩ (τ j.castSucc.succ)).val =
      SphereGreatCircle.curve a.val y.val Real.pi (τ j.castSucc.succ) at h
    rw [path_vertex, vertices_interior] at h
    exact h
  rw [he]
  exact semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hmesh y

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

include I

theorem exists_continuous_path_deformation (a b : Sphere n) (hanti : b.val = -a.val)
    (F : C(unitInterval × M, Sphere n)) (ha : ∀ x, F (0, x) = a) (hb : ∀ x, F (1, x) = b)
    (hd : finrank ℝ B + 2 < 2 * n) :
    ∃ Y : C(M, Direction a),
      Nonempty (F.HomotopyRel (semicirclePathFamily a Y)
        {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters a F}) := by
  obtain ⟨m, _, _, p, hp, E, _, hpE, ⟨G⟩⟩ :=
    exists_bounded_polygon_replacement_fixing_minima F a b ha hb hanti 1
  let cap := max (E + 1) (Real.pi ^ 2 + 1)
  have hEcap : E < cap := (by linarith : E < E + 1).trans_le (le_max_left _ _)
  have hcap : Real.pi ^ 2 < cap :=
    (by linarith : Real.pi ^ 2 < Real.pi ^ 2 + 1).trans_le (le_max_right _ _)
  obtain ⟨k, _, hk, hmesh, q, hq, hpath, henergy⟩ :=
    exists_uniform_family_refinement_with_mesh a b p hp cap 1
  have hqE : ∀ x, energy a b (time k) (q x) ≤ E := by
    intro x
    rw [henergy]
    exact hpE x
  let G' : F.HomotopyRel (realizedFamily a b (time k) (strictMono_time k) q hq)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters a F} := G.cast rfl hpath.symm
  have hqmin : ∀ x ∈ minimumPathParameters a F, q x ∈ minimumSet a b (time k) := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    apply minimum_of_realized_semicircle a b (time k) (strictMono_time k)
      (time_zero k) (time_last k) hanti
      (minimum_mesh_of_cap (time k) (strictMono_time k) cap hcap.le hmesh) q hq x y
    intro t
    have he : F (t, x) = realizedFamily a b (time k) (strictMono_time k) q hq (t, x) :=
      G'.fst_eq_snd (show (t, x) ∈ {z | z.1 = 0 ∨ z.1 = 1 ∨
        z.2 ∈ minimumPathParameters a F} from Or.inr (Or.inr ⟨y, hy⟩))
    rw [← he]
    exact hy t
  obtain ⟨Y, ⟨J⟩⟩ := exists_realized_homotopy_to_semicircles (I := I)
    a b (time k) (strictMono_time k) (time_zero k) (time_last k) hanti
    cap hcap hmesh ⟨0, hk⟩ hd q hq E hEcap hqE
  let J' : (realizedFamily a b (time k) (strictMono_time k) q hq).HomotopyRel
      (semicirclePathFamily a Y)
      {z | z.1 = 0 ∨ z.1 = 1 ∨ z.2 ∈ minimumPathParameters a F} :=
    { toHomotopy := J.toHomotopy
      prop' := by
        intro t z hz
        rcases hz with hzero | hone | hmin
        · exact J.eq_fst t (Or.inl hzero)
        · exact J.eq_fst t (Or.inr (Or.inl hone))
        · exact J.eq_fst t (Or.inr (Or.inr (hqmin z.2 hmin))) }
  exact ⟨Y, ⟨G'.trans J'⟩⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
