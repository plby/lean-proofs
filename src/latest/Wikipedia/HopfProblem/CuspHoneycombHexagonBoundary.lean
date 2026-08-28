import Wikipedia.HopfProblem.CuspHoneycombHexagonPolygon
import Wikipedia.HopfProblem.CuspHoneycombHexagonArcsCore

/-!
# The six boundary arcs of the honeycomb hexagon

Each supporting side is the literal closed segment between consecutive
vertices, with its inherited topology. The affine interval parametrizations
also identify the endpoints, and distinct sides intersect exactly when they
are consecutive.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

theorem vertex_injective : Function.Injective vertex := by
  intro i j hij
  apply ToricComponent.hexagonRay_injective
  funext k
  have h := congrFun hij k
  change (ToricComponent.hexagonRay i k : ℝ) = (ToricComponent.hexagonRay j k : ℝ) at h
  exact_mod_cast h

theorem vertex_prev_ne (k : Fin 6) : vertex (k - 1) ≠ vertex k := by
  intro h
  exact (show ∀ k : Fin 6, k - 1 ≠ k by decide) k (vertex_injective h)

/-- The side with supporting functional `k` joins the preceding vertex to
the vertex `k`. -/
theorem side_eq_segment (k : Fin 6) : side k = segment ℝ (vertex (k - 1)) (vertex k) := by
  have hpred : ∀ k : Fin 6, k - 1 =
      ![⟨5, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩,
        ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩] k := by decide
  rw [hpred k, segment_eq_image]
  ext x
  constructor
  · rintro ⟨⟨h0, h1, h01⟩, hk⟩
    obtain ⟨h0l, h0u⟩ := abs_le.mp h0
    obtain ⟨h1l, h1u⟩ := abs_le.mp h1
    obtain ⟨h01l, h01u⟩ := abs_le.mp h01
    refine ⟨![x 1 + 1, x 1, -x 0, 1 - x 1, -x 1, x 0] k, ?_, ?_⟩
    · fin_cases k <;> norm_num [sideFunctional] at hk ⊢ <;> constructor <;> linarith
    · funext j
      fin_cases k <;> fin_cases j <;>
        norm_num [sideFunctional, vertex, ToricComponent.hexagonRay,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hk ⊢ <;> linarith
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    fin_cases k <;>
      norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay,
        Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.smul_apply, smul_eq_mul, abs_le] <;>
      (repeat' constructor) <;> linarith

/-- An affine parametrization of each actual supporting side by the closed
unit interval. -/
def sideIntervalHomeomorph (k : Fin 6) : unitInterval ≃ₜ side k :=
  (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k) (vertex_prev_ne k)).trans
    (Homeomorph.setCongr (side_eq_segment k).symm)

@[simp] theorem sideIntervalHomeomorph_apply (k : Fin 6) (t : unitInterval) :
    (sideIntervalHomeomorph k t : Plane) =
      (1 - (t : ℝ)) • vertex (k - 1) + (t : ℝ) • vertex k := by
  change (segmentIntervalHomeomorph (vertex (k - 1)) (vertex k)
    (vertex_prev_ne k) t : Plane) = _
  exact segmentIntervalHomeomorph_apply _ _ _ _

@[simp] theorem sideIntervalHomeomorph_zero (k : Fin 6) :
    (sideIntervalHomeomorph k 0 : Plane) = vertex (k - 1) := by
  simp

@[simp] theorem sideIntervalHomeomorph_one (k : Fin 6) :
    (sideIntervalHomeomorph k 1 : Plane) = vertex k := by
  simp

theorem eq_vertex_of_consecutive_sideFunctional (k : Fin 6) (x : Plane)
    (h0 : sideFunctional k x = 1) (h1 : sideFunctional (k + 1) x = 1) : x = vertex k := by
  fin_cases k <;> ext l <;> fin_cases l <;>
    norm_num [sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail] at h0 h1 ⊢ <;> linarith

theorem vertex_mem_side_self (k : Fin 6) : vertex k ∈ side k := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

theorem vertex_mem_side_next (k : Fin 6) : vertex k ∈ side (k + 1) := by
  fin_cases k <;>
    norm_num [side, Hexagon, sideFunctional, vertex, ToricComponent.hexagonRay, Fin.add_def,
      Matrix.cons_val, Matrix.vecHead, Matrix.vecTail]

/-- Consecutive sides meet at their shared vertex. -/
theorem side_inter_next (k : Fin 6) : side k ∩ side (k + 1) = {vertex k} := by
  ext x
  constructor
  · intro hx
    exact eq_vertex_of_consecutive_sideFunctional k x hx.1.2 hx.2.2
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨vertex_mem_side_self k, vertex_mem_side_next k⟩

theorem side_disjoint_add_two (k : Fin 6) : Disjoint (side k) (side (k + 2)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨h0l, h0u⟩ := abs_le.mp hx.1.1
  obtain ⟨h1l, h1u⟩ := abs_le.mp hx.1.2.1
  obtain ⟨h01l, h01u⟩ := abs_le.mp hx.1.2.2
  have h0 := hx.2
  have h2 := hy.2
  fin_cases k <;>
    norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
      at h0 h2 <;>
    linarith only [h0, h2, h0l, h0u, h1l, h1u, h01l, h01u]

theorem side_disjoint_add_three (k : Fin 6) : Disjoint (side k) (side (k + 3)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h0 := hx.2
  have h3 := hy.2
  fin_cases k <;>
    norm_num [sideFunctional, Fin.add_def, Matrix.cons_val, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]
      at h0 h3 <;> linarith only [h0, h3]

theorem side_disjoint_add_four (k : Fin 6) : Disjoint (side k) (side (k + 4)) := by
  have hi : (k + 4) + 2 = k := by
    rw [add_assoc]
    change k + 0 = k
    exact add_zero k
  simpa only [hi] using (side_disjoint_add_two (k + 4)).symm

theorem side_inter_previous (k : Fin 6) : side k ∩ side (k + 5) = {vertex (k - 1)} := by
  have hi : (k + 5) + 1 = k := by
    rw [add_assoc]
    change k + 0 = k
    exact add_zero k
  have hp : k + 5 = k - 1 := by rw [sub_eq_add_neg]; rfl
  rw [inter_comm]
  simpa only [hi, hp, sub_add_cancel] using side_inter_next (k + 5)

/-- Apart from the two consecutive sides, distinct sides are disjoint. -/
theorem side_disjoint_nonadjacent {i j : Fin 6}
    (hij : i ≠ j) (hnext : j ≠ i + 1) (hprev : i ≠ j + 1) :
    Disjoint (side i) (side j) := by
  obtain ⟨k, rfl⟩ : ∃ k : Fin 6, j = i + k :=
    ⟨j - i, by rw [add_comm i (j - i), sub_add_cancel]⟩
  fin_cases k
  · exact (hij (by change i = i + 0; simp)).elim
  · exact (hnext rfl).elim
  · change Disjoint (side i) (side (i + 2))
    exact side_disjoint_add_two i
  · change Disjoint (side i) (side (i + 3))
    exact side_disjoint_add_three i
  · change Disjoint (side i) (side (i + 4))
    exact side_disjoint_add_four i
  · apply False.elim
    apply hprev
    change i = (i + 5) + 1
    rw [add_assoc]
    change i = i + 0
    exact (add_zero i).symm

end Wikipedia.HopfProblem.CuspHoneycombHexagon
