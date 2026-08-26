import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual finite congruent-triangle dissections in the Euclidean plane

The support is the closed convex hull of three affinely independent points.
Tile placements are affine isometries, including reflections. Coverage and
disjoint topological interiors are required. No edge-to-edge hypothesis or
classification assumption is part of this definition.
-/

namespace Erdos633b

abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev Triangle := Affine.Triangle ℝ Plane

namespace Triangle

def support (T : Triangle) : Set Plane := convexHull ℝ (Set.range T.points)

theorem vertex_mem_support (T : Triangle) (i : Fin 3) : T.points i ∈ T.support :=
  subset_convexHull ℝ (Set.range T.points) (Set.mem_range_self i)

theorem support_nonempty (T : Triangle) : T.support.Nonempty :=
  ⟨T.points 0, T.vertex_mem_support 0⟩

theorem support_convex (T : Triangle) : Convex ℝ T.support :=
  convex_convexHull ℝ (Set.range T.points)

theorem support_reindex (T : Triangle) (e : Equiv.Perm (Fin 3)) :
    support (T.reindex e) = T.support := by
  simp only [support, Affine.Simplex.reindex_range_points]

noncomputable def angle (T : Triangle) (i : Fin 3) : ℝ :=
  EuclideanGeometry.angle (T.points (i + 1)) (T.points i) (T.points (i + 2))

noncomputable def side (T : Triangle) (i : Fin 3) : ℝ :=
  dist (T.points (i + 1)) (T.points (i + 2))

theorem cyclic_not_collinear (T : Triangle) (i : Fin 3) :
    ¬ Collinear ℝ ({T.points (i + 1), T.points i, T.points (i + 2)} : Set Plane) := by
  apply (affineIndependent_iff_not_collinear_of_ne
    (show i + 1 ≠ i by decide +revert)
    (show i + 1 ≠ i + 2 by decide +revert)
    (show i ≠ i + 2 by decide +revert)).mp T.independent

theorem angle_pos (T : Triangle) (i : Fin 3) : 0 < T.angle i :=
  EuclideanGeometry.angle_pos_of_not_collinear (T.cyclic_not_collinear i)

theorem angle_lt_pi (T : Triangle) (i : Fin 3) : T.angle i < Real.pi :=
  EuclideanGeometry.angle_lt_pi_of_not_collinear (T.cyclic_not_collinear i)

theorem side_pos (T : Triangle) (i : Fin 3) : 0 < T.side i := by
  apply dist_pos.mpr
  exact T.independent.injective.ne (by decide +revert)

theorem angle_sum (T : Triangle) : T.angle 0 + T.angle 1 + T.angle 2 = Real.pi := by
  have hne : T.points 0 ≠ T.points 1 := T.independent.injective.ne (by decide)
  have h := EuclideanGeometry.angle_add_angle_add_angle_eq_pi (T.points 2) hne
  simpa only [angle, show (0 : Fin 3) + 1 = 1 by decide,
    show (0 : Fin 3) + 2 = 2 by decide, show (1 : Fin 3) + 1 = 2 by decide,
    show (1 : Fin 3) + 2 = 0 by decide, show (2 : Fin 3) + 1 = 0 by decide,
    show (2 : Fin 3) + 2 = 1 by decide, EuclideanGeometry.angle_comm,
    add_comm, add_left_comm, add_assoc] using h

noncomputable def move (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) : Triangle :=
  T.map g.toAffineMap g.injective

theorem support_move (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    (T.move g).support = g '' T.support := by
  change convexHull ℝ (Set.range (g ∘ T.points)) = g '' convexHull ℝ (Set.range T.points)
  rw [Set.range_comp]
  exact (g.toAffineMap.image_convexHull (Set.range T.points)).symm

theorem angle_move (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 3) :
    (T.move g).angle i = T.angle i :=
  g.toAffineIsometry.angle_map _ _ _

theorem side_move (T : Triangle) (g : Plane ≃ᵃⁱ[ℝ] Plane) (i : Fin 3) :
    (T.move g).side i = T.side i :=
  g.isometry.dist_eq _ _

end Triangle

/-- A finite dissection into mutually congruent nondegenerate triangles. -/
structure Tiling (T : Triangle) (n : ℕ) where
  tile : Triangle
  place : Fin n → Plane ≃ᵃⁱ[ℝ] Plane
  covers : (⋃ i, place i '' tile.support) = T.support
  disjoint_interiors : Pairwise fun i j =>
    Disjoint (interior (place i '' tile.support)) (interior (place j '' tile.support))

namespace Tiling

/-- Assemble a tiling from any finite index type without changing its pieces. -/
noncomputable def ofFintype {ι : Type*} [Fintype ι] (T R : Triangle)
    (f : ι → Plane ≃ᵃⁱ[ℝ] Plane) (hc : (⋃ i, f i '' R.support) = T.support)
    (hd : Pairwise fun i j => Disjoint (interior (f i '' R.support))
      (interior (f j '' R.support))) : Tiling T (Fintype.card ι) where
  tile := R
  place := fun k => f ((Fintype.equivFin ι).symm k)
  covers := by
    rw [← hc]
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨(Fintype.equivFin ι).symm k, hk⟩
    · rintro ⟨i, hi⟩
      exact ⟨Fintype.equivFin ι i, by simpa using hi⟩
  disjoint_interiors := fun _ _ h => hd ((Fintype.equivFin ι).symm.injective.ne h)

theorem piece_subset {T : Triangle} {n : ℕ} (d : Tiling T n) (i : Fin n) :
    d.place i '' d.tile.support ⊆ T.support := by
  rw [← d.covers]
  exact Set.subset_iUnion (fun j => d.place j '' d.tile.support) i

theorem positive {T : Triangle} {n : ℕ} (d : Tiling T n) : 0 < n := by
  by_contra h
  have hn : n = 0 := Nat.eq_zero_of_not_pos h
  subst n
  have he : T.support = ∅ := by simpa using d.covers.symm
  exact T.support_nonempty.ne_empty he

noncomputable def single (T : Triangle) : Tiling T 1 where
  tile := T
  place := fun _ => AffineIsometryEquiv.refl ℝ Plane
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨i, y, hy, hxy⟩
      exact hxy ▸ hy
    · intro hx
      exact ⟨0, x, hx, rfl⟩
  disjoint_interiors := by intro i j hij; exact (hij (Subsingleton.elim i j)).elim

def reindexOuter {T : Triangle} {n : ℕ} (d : Tiling T n) (e : Equiv.Perm (Fin 3)) :
    Tiling (T.reindex e) n where
  tile := d.tile
  place := d.place
  covers := by rw [Triangle.support_reindex]; exact d.covers
  disjoint_interiors := d.disjoint_interiors

/-- Move a whole dissection by a rigid motion, preserving its exact count. -/
noncomputable def move {T : Triangle} {n : ℕ} (d : Tiling T n)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    Tiling (T.move g) n where
  tile := d.tile
  place := fun i => (d.place i).trans g
  covers := by
    simp only [AffineIsometryEquiv.coe_trans, Set.image_comp,
      ← Set.image_iUnion, d.covers, Triangle.support_move]
  disjoint_interiors := by
    intro i j hij
    simp only [AffineIsometryEquiv.coe_trans, Set.image_comp]
    have hi (s : Set Plane) : g '' interior s = interior (g '' s) :=
      g.toHomeomorph.image_interior s
    rw [← hi, ← hi]
    exact Set.disjoint_image_of_injective g.injective (d.disjoint_interiors hij)

/-- Replace every tile by the same finite congruent dissection. -/
noncomputable def refine {T : Triangle} {n m : ℕ} (d : Tiling T n)
    (e : Tiling d.tile m) : Tiling T (n * m) where
  tile := e.tile
  place := fun k => (e.place (finProdFinEquiv.symm k).2).trans
    (d.place (finProdFinEquiv.symm k).1)
  covers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨k, y, hy, rfl⟩
      exact d.piece_subset (finProdFinEquiv.symm k).1
        ⟨e.place (finProdFinEquiv.symm k).2 y,
          e.piece_subset (finProdFinEquiv.symm k).2 ⟨y, hy, rfl⟩, rfl⟩
    · intro hx
      rw [← d.covers] at hx
      rcases Set.mem_iUnion.mp hx with ⟨i, z, hz, rfl⟩
      rw [← e.covers] at hz
      rcases Set.mem_iUnion.mp hz with ⟨j, y, hy, rfl⟩
      exact ⟨finProdFinEquiv (i, j), y, hy, by simp⟩
  disjoint_interiors := by
    intro k l hkl
    let i := (finProdFinEquiv.symm k : Fin n × Fin m)
    let j := (finProdFinEquiv.symm l : Fin n × Fin m)
    change Disjoint (interior ((e.place i.2).trans (d.place i.1) '' e.tile.support))
      (interior ((e.place j.2).trans (d.place j.1) '' e.tile.support))
    simp only [AffineIsometryEquiv.coe_trans, Set.image_comp]
    by_cases hij : i.1 = j.1
    · have hij' : i.2 ≠ j.2 := by
        intro h
        apply hkl
        apply finProdFinEquiv.symm.injective
        exact Prod.ext hij h
      rw [hij]
      have hi (s : Set Plane) : d.place j.1 '' interior s =
          interior (d.place j.1 '' s) := (d.place j.1).toHomeomorph.image_interior s
      rw [← hi, ← hi]
      exact Set.disjoint_image_of_injective (d.place j.1).injective
        (e.disjoint_interiors hij')
    · exact (d.disjoint_interiors hij).mono
        (interior_mono (Set.image_mono (e.piece_subset i.2)))
        (interior_mono (Set.image_mono (e.piece_subset j.2)))

end Tiling

def HasNonsquareTiling (T : Triangle) : Prop :=
  ∃ n : ℕ, ¬ IsSquare n ∧ Nonempty (Tiling T n)

def OnlySquareTilings (T : Triangle) : Prop :=
  ∀ n : ℕ, Nonempty (Tiling T n) → IsSquare n

/-- The complement formulation, independently of any classification claim. -/
theorem onlySquareTilings_iff_not_hasNonsquareTiling (T : Triangle) :
    OnlySquareTilings T ↔ ¬ HasNonsquareTiling T := by
  classical
  simp only [OnlySquareTilings, HasNonsquareTiling, not_exists, not_and]
  exact forall_congr' fun n => ⟨fun h hn ht => hn (h ht), fun h ht =>
    Classical.byContradiction fun hn => h hn ht⟩

end Erdos633b
