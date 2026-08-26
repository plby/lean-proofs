import ErdosProblems.Erdos633.BarycentricGeometry

/-!
# The local cones of a dissection form an actual partition

Positive homotheties preserve the active barycentric inequalities. This
turns the verified local neighborhood model into a global cover by incident
tile cones, with pairwise disjoint open cones.
-/

namespace Erdos633

open scoped Topology

theorem Triangle.barycentric_lineMap (P : Triangle) (z x : ℂ) (t : ℝ) (i : Fin 3) :
    P.barycentric (AffineMap.lineMap z x t) i =
      (1 - t) * P.barycentric z i + t * P.barycentric x i := by
  have h := P.coordinateEquiv.symm.toAffineMap.apply_lineMap z x t
  change P.coordinateEquiv.symm (AffineMap.lineMap z x t) =
    AffineMap.lineMap (P.coordinateEquiv.symm z) (P.coordinateEquiv.symm x) t at h
  fin_cases i <;> dsimp [Triangle.barycentric] <;> rw [h] <;>
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.add_re,
      Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.smul_re, Complex.smul_im,
      smul_eq_mul] <;> ring

theorem Triangle.localConeAt_lineMap_iff (P : Triangle) (z x : ℂ) (t : ℝ) (ht : 0 < t) :
    AffineMap.lineMap z x t ∈ P.localConeAt z ↔ x ∈ P.localConeAt z := by
  constructor
  · intro h i hi
    have hh := h i hi
    rw [P.barycentric_lineMap, hi, mul_zero, zero_add] at hh
    exact nonneg_of_mul_nonneg_right hh ht
  · intro h i hi
    rw [P.barycentric_lineMap, hi, mul_zero, zero_add]
    exact mul_nonneg ht.le (h i hi)

theorem Triangle.localOpenConeAt_lineMap_iff (P : Triangle) (z x : ℂ) (t : ℝ) (ht : 0 < t) :
    AffineMap.lineMap z x t ∈ P.localOpenConeAt z ↔ x ∈ P.localOpenConeAt z := by
  constructor
  · intro h i hi
    have hh := h i hi
    rw [P.barycentric_lineMap, hi, mul_zero, zero_add] at hh
    exact pos_of_mul_pos_right hh ht.le
  · intro h i hi
    rw [P.barycentric_lineMap, hi, mul_zero, zero_add]
    exact mul_pos ht (h i hi)

theorem exists_positive_lineMap_mem_ball (z x : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ AffineMap.lineMap z x t ∈ Metric.ball z ε := by
  let t : ℝ := ε / (2 * (dist x z + 1))
  have hd : 0 < 2 * (dist x z + 1) := by positivity
  have ht : 0 < t := div_pos hε hd
  have heq : t * (2 * (dist x z + 1)) = ε := div_mul_cancel₀ ε (ne_of_gt hd)
  have hdist : dist (AffineMap.lineMap z x t) z = t * dist x z := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, dist_eq_norm,
      add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨t, ht, ?_⟩
  rw [Metric.mem_ball, hdist]
  nlinarith only [heq, ht, mul_nonneg ht.le (dist_nonneg : 0 ≤ dist x z)]

theorem Triangle.eventually_local_cone_iff (P : Triangle) (z : ℂ) (hz : z ∈ P.carrier) :
    ∀ᶠ x in 𝓝 z, (x ∈ P.carrier ↔ x ∈ P.localConeAt z) ∧
      (x ∈ interior P.carrier ↔ x ∈ P.localOpenConeAt z) := by
  obtain ⟨ε, hε, hball⟩ := P.exists_local_cone_radius z hz
  exact Filter.mem_of_superset (Metric.ball_mem_nhds z hε) hball

theorem TriangleDissection.local_cone_model {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Metric.ball z ε,
      (x ∈ P.carrier ↔ x ∈ P.localConeAt z) ∧
      (∀ i : Fin N, z ∈ (T.tile i).carrier →
        (x ∈ (T.tile i).carrier ↔ x ∈ (T.tile i).localConeAt z) ∧
        (x ∈ interior (T.tile i).carrier ↔ x ∈ (T.tile i).localOpenConeAt z)) ∧
      (∀ i : Fin N, x ∈ (T.tile i).carrier → z ∈ (T.tile i).carrier) := by
  have hP := (P.eventually_local_cone_iff z hz).mono fun _ h => h.1
  have htiles : ∀ᶠ x in 𝓝 z, ∀ i : Fin N, z ∈ (T.tile i).carrier →
      (x ∈ (T.tile i).carrier ↔ x ∈ (T.tile i).localConeAt z) ∧
      (x ∈ interior (T.tile i).carrier ↔ x ∈ (T.tile i).localOpenConeAt z) := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : z ∈ (T.tile i).carrier
    · exact ((T.tile i).eventually_local_cone_iff z hi).mono fun _ h _ => h
    · exact Filter.Eventually.of_forall fun _ h => False.elim (hi h)
  obtain ⟨ε, hε, hlocal⟩ := T.exists_local_incidence_radius z
  have hincident : ∀ᶠ x in 𝓝 z, ∀ i : Fin N,
      x ∈ (T.tile i).carrier → z ∈ (T.tile i).carrier :=
    Filter.mem_of_superset (Metric.ball_mem_nhds z hε) hlocal
  exact Metric.mem_nhds_iff.mp (hP.and (htiles.and hincident))

theorem TriangleDissection.localConeAt_eq_union {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localConeAt z = ⋃ (i : Fin N) (_ : z ∈ (T.tile i).carrier), (T.tile i).localConeAt z := by
  obtain ⟨ε, hε, hmodel⟩ := T.local_cone_model z hz
  ext x
  obtain ⟨t, ht, hnear⟩ := exists_positive_lineMap_mem_ball z x ε hε
  obtain ⟨hP, htiles, hincident⟩ := hmodel _ hnear
  constructor
  · intro hx
    have hyP : AffineMap.lineMap z x t ∈ P.carrier :=
      hP.mpr ((P.localConeAt_lineMap_iff z x t ht).mpr hx)
    rw [← T.covers, Set.mem_iUnion] at hyP
    obtain ⟨i, hi⟩ := hyP
    have hzi := hincident i hi
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hzi, ?_⟩⟩
    exact ((T.tile i).localConeAt_lineMap_iff z x t ht).mp ((htiles i hzi).1.mp hi)
  · intro hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hzi, hi⟩ := Set.mem_iUnion.mp hx
    have hyi : AffineMap.lineMap z x t ∈ (T.tile i).carrier :=
      (htiles i hzi).1.mpr (((T.tile i).localConeAt_lineMap_iff z x t ht).mpr hi)
    exact (P.localConeAt_lineMap_iff z x t ht).mp (hP.mp (T.tile_subset i hyi))

theorem TriangleDissection.localOpenConeAt_disjoint {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) {i j : Fin N} (hij : i ≠ j)
    (hi : z ∈ (T.tile i).carrier) (hj : z ∈ (T.tile j).carrier) :
    Disjoint ((T.tile i).localOpenConeAt z) ((T.tile j).localOpenConeAt z) := by
  obtain ⟨ε, hε, hmodel⟩ := T.local_cone_model z (T.tile_subset i hi)
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨t, ht, hnear⟩ := exists_positive_lineMap_mem_ball z x ε hε
  have htiles := (hmodel _ hnear).2.1
  have hyi : AffineMap.lineMap z x t ∈ interior (T.tile i).carrier :=
    (htiles i hi).2.mpr (((T.tile i).localOpenConeAt_lineMap_iff z x t ht).mpr hxi)
  have hyj : AffineMap.lineMap z x t ∈ interior (T.tile j).carrier :=
    (htiles j hj).2.mpr (((T.tile j).localOpenConeAt_lineMap_iff z x t ht).mpr hxj)
  exact Set.disjoint_left.mp (T.disjoint hij) hyi hyj

end Erdos633
