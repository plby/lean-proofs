import ErdosProblems.Erdos633.LocalGeometry

/-!
# Barycentric inequalities and local triangle cones

Near a point of a triangle, only the barycentric inequalities that vanish
at that point can constrain membership. This identifies the local closed
region and its interior using actual affine coordinates.
-/

namespace Erdos633

open scoped BigOperators Topology

noncomputable def Triangle.barycentric (P : Triangle) (z : ℂ) : Fin 3 → ℝ :=
  ![1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im,
    (P.coordinateEquiv.symm z).re, (P.coordinateEquiv.symm z).im]

theorem Triangle.sum_barycentric (P : Triangle) (z : ℂ) : ∑ i, P.barycentric z i = 1 := by
  simp only [Triangle.barycentric, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  ring

theorem Triangle.barycentric_continuous (P : Triangle) (i : Fin 3) :
    Continuous (fun z => P.barycentric z i) := by
  have hc : Continuous P.coordinateEquiv.symm :=
    P.coordinateEquiv.symm.toContinuousAffineEquiv.continuous
  have hr := Complex.continuous_re.comp hc
  have hi := Complex.continuous_im.comp hc
  fin_cases i
  · exact (continuous_const.sub hr).sub hi
  · exact hr
  · exact hi

theorem Triangle.mem_carrier_iff_coordinates (P : Triangle) (z : ℂ) :
    z ∈ P.carrier ↔ 0 ≤ (P.coordinateEquiv.symm z).re ∧
      0 ≤ (P.coordinateEquiv.symm z).im ∧
      (P.coordinateEquiv.symm z).re + (P.coordinateEquiv.symm z).im ≤ 1 := by
  have hmap : P.coordinateEquiv '' standardTriangle.carrier = P.carrier := by
    rw [← Triangle.mapAffineEquiv_carrier, P.standard_map_coordinateEquiv]
  rw [← hmap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [P.coordinateEquiv.symm_apply_apply]
    rw [standardTriangle_carrier] at hw
    exact hw
  · intro hz
    exact ⟨P.coordinateEquiv.symm z, standardTriangle_carrier.symm ▸ hz,
      P.coordinateEquiv.apply_symm_apply z⟩

theorem Triangle.mem_interior_iff_coordinates (P : Triangle) (z : ℂ) :
    z ∈ interior P.carrier ↔ 0 < (P.coordinateEquiv.symm z).re ∧
      0 < (P.coordinateEquiv.symm z).im ∧
      (P.coordinateEquiv.symm z).re + (P.coordinateEquiv.symm z).im < 1 := by
  have hmap : P.coordinateEquiv '' interior standardTriangle.carrier = interior P.carrier := by
    rw [← Triangle.mapAffineEquiv_interior, P.standard_map_coordinateEquiv]
  rw [← hmap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [P.coordinateEquiv.symm_apply_apply]
    rw [standardTriangle_interior] at hw
    exact hw
  · intro hz
    exact ⟨P.coordinateEquiv.symm z, standardTriangle_interior.symm ▸ hz,
      P.coordinateEquiv.apply_symm_apply z⟩

theorem Triangle.mem_carrier_iff_barycentric (P : Triangle) (z : ℂ) :
    z ∈ P.carrier ↔ ∀ i, 0 ≤ P.barycentric z i := by
  rw [P.mem_carrier_iff_coordinates]
  constructor
  · intro h i
    fin_cases i
    · change 0 ≤ 1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im
      linarith [h.2.2]
    · exact h.1
    · exact h.2.1
  · intro h
    have h0 := h 0
    change 0 ≤ 1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im at h0
    exact ⟨h 1, h 2, by linarith⟩

theorem Triangle.mem_interior_iff_barycentric (P : Triangle) (z : ℂ) :
    z ∈ interior P.carrier ↔ ∀ i, 0 < P.barycentric z i := by
  rw [P.mem_interior_iff_coordinates]
  constructor
  · intro h i
    fin_cases i
    · change 0 < 1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im
      linarith [h.2.2]
    · exact h.1
    · exact h.2.1
  · intro h
    have h0 := h 0
    change 0 < 1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im at h0
    exact ⟨h 1, h 2, by linarith⟩

noncomputable def Triangle.localConeAt (P : Triangle) (z : ℂ) : Set ℂ :=
  {x | ∀ i, P.barycentric z i = 0 → 0 ≤ P.barycentric x i}

noncomputable def Triangle.localOpenConeAt (P : Triangle) (z : ℂ) : Set ℂ :=
  {x | ∀ i, P.barycentric z i = 0 → 0 < P.barycentric x i}

theorem Triangle.exists_local_cone_radius (P : Triangle) (z : ℂ) (hz : z ∈ P.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball z ε,
      (x ∈ P.carrier ↔ x ∈ P.localConeAt z) ∧
      (x ∈ interior P.carrier ↔ x ∈ P.localOpenConeAt z) := by
  have hz0 := (P.mem_carrier_iff_barycentric z).mp hz
  have hnear : ∀ᶠ x in 𝓝 z, ∀ i : Fin 3,
      P.barycentric z i ≠ 0 → 0 < P.barycentric x i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : P.barycentric z i = 0
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hi)
    · have hp : 0 < P.barycentric z i := lt_of_le_of_ne (hz0 i) (Ne.symm hi)
      have hn := (isOpen_lt continuous_const (P.barycentric_continuous i)).mem_nhds hp
      exact Filter.Eventually.mono hn fun _ hx _ => hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨ε, hε, ?_⟩
  intro x hx
  constructor
  · rw [P.mem_carrier_iff_barycentric]
    constructor
    · intro h i _
      exact h i
    · intro h i
      by_cases hi : P.barycentric z i = 0
      · exact h i hi
      · exact (hball hx i hi).le
  · rw [P.mem_interior_iff_barycentric]
    constructor
    · intro h i _
      exact h i
    · intro h i
      by_cases hi : P.barycentric z i = 0
      · exact h i hi
      · exact hball hx i hi

end Erdos633
