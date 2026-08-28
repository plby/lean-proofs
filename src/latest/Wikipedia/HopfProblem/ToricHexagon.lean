import Wikipedia.HopfProblem.ToricComponentTopology

/-!+# The six charts and hexagonal star at the zero ray

This explicitly enumerates every triangle containing the zero vertex. The
remaining vertices are consecutive rays of the smooth hexagon. These facts
concern the actual coordinate charts of `E₀`; they do not assume its
identification with a blow-up of the projective plane.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricFan ToricSpace Triangle

def zeroTriangle : Fin 6 → Triangle :=
  ![⟨0, 0, false⟩, ⟨-1, 0, true⟩, ⟨-1, 0, false⟩,
    ⟨-1, -1, true⟩, ⟨0, -1, false⟩, ⟨0, -1, true⟩]

def zeroCoordinate : Fin 6 → Fin 3 := ![0, 0, 1, 2, 2, 1]

theorem zeroTriangle_vertex (i : Fin 6) : (zeroTriangle i).vertex (zeroCoordinate i) = 0 := by
  fin_cases i <;> decide

def zeroChart (i : Fin 6) : ChartIndex 0 :=
  ⟨zeroTriangle i, zeroCoordinate i, zeroTriangle_vertex i⟩

theorem zeroChart_surjective : Function.Surjective zeroChart := by
  rintro ⟨⟨a, b, u⟩, j, hj⟩
  have h0 := congrFun hj 0
  have h1 := congrFun hj 1
  cases u <;> fin_cases j
  · change a = 0 at h0
    change b = 0 at h1
    subst a b
    exact ⟨0, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨2, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨4, rfl⟩
  · change a + 1 = 0 at h0
    change b = 0 at h1
    have ha : a = -1 := by omega
    subst a b
    exact ⟨1, rfl⟩
  · change a = 0 at h0
    change b + 1 = 0 at h1
    have hb : b = -1 := by omega
    subst a b
    exact ⟨5, rfl⟩
  · change a + 1 = 0 at h0
    change b + 1 = 0 at h1
    have ha : a = -1 := by omega
    have hb : b = -1 := by omega
    subst a b
    exact ⟨3, rfl⟩

theorem zeroChart_injective : Function.Injective zeroChart := by
  have h : Function.Injective (fun i : Fin 6 => (zeroTriangle i, zeroCoordinate i)) := by decide
  intro i j hij
  exact h (congrArg (fun c : ChartIndex 0 => (c.triangle, c.coordinate)) hij)

def zeroChartEquiv : Fin 6 ≃ ChartIndex 0 := Equiv.ofBijective zeroChart
  ⟨zeroChart_injective, zeroChart_surjective⟩

theorem zero_chart_count : Nat.card (ChartIndex 0) = 6 := by
  rw [← Nat.card_congr zeroChartEquiv, Nat.card_fin]

theorem zeroChart_cover : (⋃ i : Fin 6, range (affineInclusion (zeroChart i))) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨c, z, rfl⟩ := affineInclusion_jointly_surjective x
  obtain ⟨i, rfl⟩ := zeroChart_surjective c
  exact mem_iUnion.mpr ⟨i, mem_range_self z⟩

/-- The cyclic list `e₁, e₂, e₂-e₁, -e₁, -e₂, e₁-e₂`. -/
def hexagonRay : Fin 6 → (Fin 2 → ℤ) :=
  ![![1, 0], ![0, 1], ![-1, 1], ![-1, 0], ![0, -1], ![1, -1]]

theorem hexagonRay_injective : Function.Injective hexagonRay := by decide

theorem hexagonRay_ne_zero (i : Fin 6) : hexagonRay i ≠ 0 := by
  fin_cases i <;> decide

theorem zeroTriangle_vertices (i : Fin 6) :
    range (zeroTriangle i).vertex = {0, hexagonRay i, hexagonRay (i + 1)} := by
  have h : Finset.univ.image (zeroTriangle i).vertex =
      {0, hexagonRay i, hexagonRay (i + 1)} := by
    fin_cases i <;> decide
  simpa only [Finset.coe_image, Finset.coe_univ, image_univ,
    Finset.coe_insert, Finset.coe_singleton] using
    congrArg (fun s : Finset (Fin 2 → ℤ) => (s : Set (Fin 2 → ℤ))) h

theorem hexagonRay_opposite (i : Fin 6) : hexagonRay (i + 3) = -hexagonRay i := by
  fin_cases i <;> decide

theorem hexagonRay_relation (i : Fin 6) :
    hexagonRay (i + 2) = hexagonRay (i + 1) - hexagonRay i := by
  fin_cases i <;> decide

theorem hexagonRay_consecutive_det (i : Fin 6) :
    Matrix.det (!![hexagonRay i 0, hexagonRay (i + 1) 0;
      hexagonRay i 1, hexagonRay (i + 1) 1]) = 1 := by
  rw [Matrix.det_fin_two]
  fin_cases i <;> decide

end Wikipedia.HopfProblem.ToricComponent
