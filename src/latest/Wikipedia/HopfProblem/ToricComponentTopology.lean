import Wikipedia.HopfProblem.ToricComponentManifold
import Wikipedia.HopfProblem.CuspComponentInterior

/-!+# Connectedness of the compact central components

The open torus of any coordinate hyperplane lies in every chart belonging
to the same ray. Thus all these connected affine charts have a common point,
and their union, the actual ray surface, is connected.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

variable {v : Fin 2 → ℤ}

theorem insertZero_ne_of_ne (j : Fin 3) {z : CoordinateSpace 2} (hz : z ∈ torus)
    {k : Fin 3} (hk : k ≠ j) : insertZero j z k ≠ 0 := by
  obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k
  · exact (hk rfl).elim
  · simpa only [insertZero, Fin.insertNth_apply_succAbove] using hz l

theorem insertZero_torus_mem_source (c d : ChartIndex v) {z : CoordinateSpace 2}
    (hz : z ∈ torus) : insertZero c.coordinate z ∈ (chartChange c.triangle d.triangle).source := by
  rw [chartChange_source]
  intro i j hij
  apply insertZero_ne_of_ne c.coordinate hz
  intro hj
  subst j
  have hcol := (transition_column_iff_vertex c.triangle d.triangle
    c.coordinate d.coordinate).mpr (c.vertex_eq.trans d.vertex_eq.symm) i
  rw [hcol] at hij
  split_ifs at hij <;> omega

theorem affineInclusion_mem_range_iff (c : ChartIndex v) (x : rayDivisor v) :
    x ∈ range (affineInclusion c) ↔ (x : Space) ∈ range (inclusion c.triangle) := by
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨insertZero c.coordinate z, rfl⟩
  · rintro ⟨z, hz⟩
    have hm : inclusion c.triangle z ∈ rayDivisor v := hz ▸ x.2
    have hj : z c.coordinate = 0 :=
      (mem_rayDivisor_vertex c.triangle c.coordinate z).mp
        (by simpa only [c.vertex_eq] using hm)
    refine ⟨removeCoordinate c.coordinate z, Subtype.ext ?_⟩
    change inclusion c.triangle (insertZero c.coordinate (removeCoordinate c.coordinate z)) = _
    rw [insertZero_removeCoordinate _ _ hj]
    exact hz

theorem affineInclusion_torus_mem_range (c d : ChartIndex v) {z : CoordinateSpace 2}
    (hz : z ∈ torus) : affineInclusion c z ∈ range (affineInclusion d) := by
  rw [affineInclusion_mem_range_iff]
  refine ⟨chartChange c.triangle d.triangle (insertZero c.coordinate z), ?_⟩
  exact ((inclusion_eq_iff c.triangle d.triangle _ _).mpr
    ⟨insertZero_torus_mem_source c d hz, rfl⟩).symm

def baseChart (v : Fin 2 → ℤ) : ChartIndex v where
  triangle := ⟨v 0, v 1, false⟩
  coordinate := 0
  vertex_eq := by ext i; fin_cases i <;> simp [vertex, rays]

instance component_nonempty (v : Fin 2 → ℤ) : Nonempty (rayDivisor v) :=
  ⟨affineInclusion (baseChart v) 0⟩

theorem affineInclusions_cover (v : Fin 2 → ℤ) :
    (⋃ c : ChartIndex v, range (affineInclusion c)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
  exact mem_iUnion.mpr ⟨c, mem_range_self z⟩

instance component_preconnectedSpace (v : Fin 2 → ℤ) : PreconnectedSpace (rayDivisor v) := by
  constructor
  rw [← affineInclusions_cover v]
  apply isPreconnected_iUnion
  · refine ⟨affineInclusion (baseChart v) (fun _ => 1), mem_iInter.mpr fun c => ?_⟩
    exact affineInclusion_torus_mem_range (baseChart v) c (fun _ => one_ne_zero)
  · intro c
    exact isPreconnected_range (affineInclusion_openEmbedding c).continuous

instance component_connectedSpace (v : Fin 2 → ℤ) : ConnectedSpace (rayDivisor v) :=
  { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

end Wikipedia.HopfProblem.ToricComponent
