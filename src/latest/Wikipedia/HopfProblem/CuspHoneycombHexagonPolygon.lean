import Wikipedia.HopfProblem.CuspHoneycombHexagonSquare
import Wikipedia.HopfProblem.ToricHexagon

/-!
# Six explicit piecewise-linear tiles of the real hexagon

The square maps use the six integral rays of the actual zero component.
Their common-edge identifications are recorded by the same `SquareRel`
used for the oriented toric charts.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

/-- The real vertices of the hexagonal fan. -/
def vertex (i : Fin 6) : Plane := fun k => (ToricComponent.hexagonRay i k : ℝ)

/-- The midpoint of the edge from the previous vertex to the current one. -/
def midpoint (i : Fin 6) : Plane := (1 / 2 : ℝ) • (vertex (i - 1) + vertex i)

/-- The literal closed hexagonal region in the real plane. -/
def Hexagon : Set Plane := {x | |x 0| ≤ 1 ∧ |x 1| ≤ 1 ∧ |x 0 + x 1| ≤ 1}

/-- Supporting functions, numbered by the edge from `vertex (k - 1)`
to `vertex k`. -/
def sideFunctional (k : Fin 6) (x : Plane) : ℝ :=
  ![x 0, x 0 + x 1, x 1, -x 0, -x 0 - x 1, -x 1] k

/-- The actual closed side of the hexagonal region. -/
def side (k : Fin 6) : Set Plane := {x | x ∈ Hexagon ∧ sideFunctional k x = 1}

@[simp] theorem sideFunctional_zero (x : Plane) : sideFunctional 0 x = x 0 := rfl
@[simp] theorem sideFunctional_one (x : Plane) : sideFunctional 1 x = x 0 + x 1 := rfl
@[simp] theorem sideFunctional_two (x : Plane) : sideFunctional 2 x = x 1 := rfl
@[simp] theorem sideFunctional_three (x : Plane) : sideFunctional 3 x = -x 0 := rfl
@[simp] theorem sideFunctional_four (x : Plane) : sideFunctional 4 x = -x 0 - x 1 := rfl
@[simp] theorem sideFunctional_five (x : Plane) : sideFunctional 5 x = -x 1 := rfl

def cornerZero : Square := ⟨fun _ => 0, fun _ => ⟨le_rfl, zero_le_one⟩⟩

def cornerOne : Square := ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩⟩

/-- The two affine triangles of one quadrilateral tile, joined along the
diagonal from its outer vertex to the common center. -/
def tile (i : Fin 6) (p : Square) : Plane :=
  (1 - max (p.1 0) (p.1 1)) • vertex i +
    max (p.1 1 - p.1 0) 0 • midpoint i +
    max (p.1 0 - p.1 1) 0 • midpoint (i + 1)

theorem tile_continuous (i : Fin 6) : Continuous (tile i) := by
  have h0 : Continuous (fun p : Square => p.1 0) :=
    (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous (fun p : Square => p.1 1) :=
    (continuous_apply 1).comp continuous_subtype_val
  exact (((continuous_const.sub (h0.max h1)).smul continuous_const).add
    (((h1.sub h0).max continuous_const).smul continuous_const)).add
      (((h0.sub h1).max continuous_const).smul continuous_const)

theorem tile_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p = (1 - p.1 1) • vertex i + (p.1 1 - p.1 0) • midpoint i := by
  simp only [tile, max_eq_right hp, max_eq_left (sub_nonneg.mpr hp),
    max_eq_right (sub_nonpos.mpr hp), zero_smul, add_zero]

theorem tile_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - p.1 0) • vertex i + (p.1 0 - p.1 1) • midpoint (i + 1) := by
  simp only [tile, max_eq_left hp, max_eq_right (sub_nonpos.mpr hp),
    max_eq_left (sub_nonneg.mpr hp), zero_smul, add_zero]

theorem tile_fst_one (i : Fin 6) (p : Square) (hp : p.1 0 = 1) :
    tile i p = (1 - p.1 1) • midpoint (i + 1) := by
  rw [tile_of_ge i p (by simpa only [hp] using (p.2 1).2)]
  simp only [hp, sub_self, zero_smul, zero_add]

theorem tile_snd_one (i : Fin 6) (p : Square) (hp : p.1 1 = 1) :
    tile i p = (1 - p.1 0) • midpoint i := by
  rw [tile_of_le i p (by simpa only [hp] using (p.2 0).2)]
  simp only [hp, sub_self, zero_smul, zero_add]

theorem tile_fst_zero (i : Fin 6) (p : Square) (hp : p.1 0 = 0) :
    tile i p = (1 - p.1 1) • vertex i + p.1 1 • midpoint i := by
  rw [tile_of_le i p (by simpa only [hp] using (p.2 1).1)]
  simp only [hp, sub_zero]

theorem tile_snd_zero (i : Fin 6) (p : Square) (hp : p.1 1 = 0) :
    tile i p = (1 - p.1 0) • vertex i + p.1 0 • midpoint (i + 1) := by
  rw [tile_of_ge i p (by simpa only [hp] using (p.2 0).1)]
  simp only [hp, sub_zero]

@[simp] theorem tile_cornerZero (i : Fin 6) : tile i cornerZero = vertex i := by
  rw [tile_fst_zero i cornerZero rfl]
  simp only [cornerZero, sub_zero, one_smul, zero_smul, add_zero]

@[simp] theorem tile_cornerOne (i : Fin 6) : tile i cornerOne = 0 := by
  rw [tile_fst_one i cornerOne rfl]
  simp only [cornerOne, sub_self, zero_smul]

@[simp] theorem vertex_zero : vertex 0 = ![1, 0] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp] theorem vertex_one : vertex 1 = ![0, 1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp] theorem vertex_two : vertex 2 = ![-1, 1] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((1 : ℤ) : ℝ) = 1
    norm_num

@[simp] theorem vertex_three : vertex 3 = ![-1, 0] := by
  funext k
  fin_cases k
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num
  · change ((0 : ℤ) : ℝ) = 0
    norm_num

@[simp] theorem vertex_four : vertex 4 = ![0, -1] := by
  funext k
  fin_cases k
  · change ((0 : ℤ) : ℝ) = 0
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

@[simp] theorem vertex_five : vertex 5 = ![1, -1] := by
  funext k
  fin_cases k
  · change ((1 : ℤ) : ℝ) = 1
    norm_num
  · change ((-1 : ℤ) : ℝ) = -1
    norm_num

/-- The order-six integral rotation of this hexagon. -/
def rotate : Plane ≃ₗ[ℝ] Plane where
  toFun x := ![-x 1, x 0 + x 1]
  invFun x := ![x 0 + x 1, -x 0]
  left_inv x := by
    funext k
    fin_cases k <;> simp
  right_inv x := by
    funext k
    fin_cases k <;> simp
  map_add' x y := by
    funext k
    fin_cases k <;> simp <;> ring
  map_smul' r x := by
    funext k
    fin_cases k <;> simp <;> ring

@[simp] theorem rotate_vertex (i : Fin 6) : rotate (vertex i) = vertex (i + 1) := by
  have hr : ∀ i : Fin 6,
      ToricComponent.hexagonRay (i + 1) 0 = -ToricComponent.hexagonRay i 1 ∧
      ToricComponent.hexagonRay (i + 1) 1 =
        ToricComponent.hexagonRay i 0 + ToricComponent.hexagonRay i 1 := by decide
  funext k
  fin_cases k
  · change -(ToricComponent.hexagonRay i 1 : ℝ) =
      (ToricComponent.hexagonRay (i + 1) 0 : ℝ)
    rw [(hr i).1, Int.cast_neg]
  · change (ToricComponent.hexagonRay i 0 : ℝ) + (ToricComponent.hexagonRay i 1 : ℝ) =
      (ToricComponent.hexagonRay (i + 1) 1 : ℝ)
    rw [(hr i).2, Int.cast_add]

@[simp] theorem rotate_midpoint (i : Fin 6) : rotate (midpoint i) = midpoint (i + 1) := by
  simp only [midpoint, map_smul, map_add, rotate_vertex, sub_add_cancel, add_sub_cancel_right]

@[simp] theorem rotate_tile (i : Fin 6) (p : Square) : rotate (tile i p) = tile (i + 1) p := by
  simp only [tile, map_add, map_smul, rotate_vertex, rotate_midpoint]

theorem sector_formula_0 (α β : ℝ) :
    α • vertex 0 + β • vertex (0 + 1) = ![α, β] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]

theorem sector_formula_1 (α β : ℝ) :
    α • vertex 1 + β • vertex (1 + 1) = ![-β, α + β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]

theorem sector_formula_2 (α β : ℝ) :
    α • vertex 2 + β • vertex (2 + 1) = ![-α - β, α] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]
  · change α * ((1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = α
    norm_num [sub_eq_add_neg]

theorem sector_formula_3 (α β : ℝ) :
    α • vertex 3 + β • vertex (3 + 1) = ![-α, -β] := by
  ext k
  fin_cases k
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]
  · change α * ((0 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -β
    norm_num [sub_eq_add_neg]

theorem sector_formula_4 (α β : ℝ) :
    α • vertex 4 + β • vertex (4 + 1) = ![β, -α - β] := by
  ext k
  fin_cases k
  · change α * ((0 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((-1 : ℤ) : ℝ) = -α - β
    norm_num [sub_eq_add_neg]

theorem sector_formula_5 (α β : ℝ) :
    α • vertex 5 + β • vertex (5 + 1) = ![α + β, -α] := by
  ext k
  fin_cases k
  · change α * ((1 : ℤ) : ℝ) + β * ((1 : ℤ) : ℝ) = α + β
    norm_num [sub_eq_add_neg]
  · change α * ((-1 : ℤ) : ℝ) + β * ((0 : ℤ) : ℝ) = -α
    norm_num [sub_eq_add_neg]

theorem sector_decomposition {x : Plane} (hx : x ∈ Hexagon) :
    ∃ i : Fin 6, ∃ α β : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ x = α • vertex i + β • vertex (i + 1) := by
  obtain ⟨h0, h1, h01⟩ := hx
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h01l, h01u⟩ := abs_le.mp h01
  by_cases ha : 0 ≤ x 0
  · by_cases hb : 0 ≤ x 1
    · refine ⟨0, x 0, x 1, ha, hb, h01u, ?_⟩
      rw [sector_formula_0]
      exact funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨5, -x 1, x 0 + x 1, ?_, hab, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_5]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
      · refine ⟨4, -(x 0 + x 1), x 0, ?_, ha, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_4]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
  · by_cases hb : 0 ≤ x 1
    · by_cases hab : 0 ≤ x 0 + x 1
      · refine ⟨1, x 0 + x 1, -x 0, hab, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_1]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
      · refine ⟨2, x 1, -(x 0 + x 1), hb, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [sector_formula_2]
          refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring
    · refine ⟨3, -x 0, -x 1, ?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · rw [sector_formula_3]
        refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

theorem sector_mem_hexagon (i : Fin 6) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    α • vertex i + β • vertex (i + 1) ∈ Hexagon := by
  fin_cases i
  · change α • vertex 0 + β • vertex (0 + 1) ∈ Hexagon
    rw [sector_formula_0]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 1 + β • vertex (1 + 1) ∈ Hexagon
    rw [sector_formula_1]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 2 + β • vertex (2 + 1) ∈ Hexagon
    rw [sector_formula_2]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 3 + β • vertex (3 + 1) ∈ Hexagon
    rw [sector_formula_3]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 4 + β • vertex (4 + 1) ∈ Hexagon
    rw [sector_formula_4]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · change α • vertex 5 + β • vertex (5 + 1) ∈ Hexagon
    rw [sector_formula_5]
    simp only [Hexagon, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, abs_le]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

theorem mem_hexagon_iff {x : Plane} :
    x ∈ Hexagon ↔ ∃ i : Fin 6, ∃ α β : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ α + β ≤ 1 ∧ x = α • vertex i + β • vertex (i + 1) := by
  constructor
  · exact sector_decomposition
  · rintro ⟨i, α, β, hα, hβ, hαβ, rfl⟩
    exact sector_mem_hexagon i hα hβ hαβ

theorem tile_zero_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 0 p = ![1 - p.1 0, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_le 0 p h]
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_zero_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 0 p = ![1 - (p.1 0 + p.1 1) / 2, (p.1 0 - p.1 1) / 2] := by
  rw [tile_of_ge 0 p h]
  have hadd : (0 : Fin 6) + 1 = 1 := by decide
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [hadd, midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_one_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_le 1 p h]
  have hindex : (1 : Fin 6) - 1 = 0 := by decide
  rw [midpoint, hindex, vertex_zero, vertex_one]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_one_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 1 p = ![(p.1 1 - p.1 0) / 2, 1 - p.1 1] := by
  rw [tile_of_ge 1 p h]
  have hadd : (1 : Fin 6) + 1 = 2 := by decide
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [hadd, midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_two_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 2 p = ![(p.1 0 + p.1 1) / 2 - 1, 1 - p.1 0] := by
  rw [tile_of_le 2 p h]
  have hindex : (2 : Fin 6) - 1 = 1 := by decide
  rw [midpoint, hindex, vertex_one, vertex_two]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_two_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 2 p = ![p.1 1 - 1, 1 - (p.1 0 + p.1 1) / 2] := by
  rw [tile_of_ge 2 p h]
  have hadd : (2 : Fin 6) + 1 = 3 := by decide
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [hadd, midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_three_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 3 p = ![p.1 0 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_le 3 p h]
  have hindex : (3 : Fin 6) - 1 = 2 := by decide
  rw [midpoint, hindex, vertex_two, vertex_three]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_three_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 3 p = ![(p.1 0 + p.1 1) / 2 - 1, (p.1 1 - p.1 0) / 2] := by
  rw [tile_of_ge 3 p h]
  have hadd : (3 : Fin 6) + 1 = 4 := by decide
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [hadd, midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_four_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_le 4 p h]
  have hindex : (4 : Fin 6) - 1 = 3 := by decide
  rw [midpoint, hindex, vertex_three, vertex_four]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_four_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 4 p = ![(p.1 0 - p.1 1) / 2, p.1 1 - 1] := by
  rw [tile_of_ge 4 p h]
  have hadd : (4 : Fin 6) + 1 = 5 := by decide
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [hadd, midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_five_le (p : Square) (h : p.1 0 ≤ p.1 1) :
    tile 5 p = ![1 - (p.1 0 + p.1 1) / 2, p.1 0 - 1] := by
  rw [tile_of_le 5 p h]
  have hindex : (5 : Fin 6) - 1 = 4 := by decide
  rw [midpoint, hindex, vertex_four, vertex_five]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem tile_five_ge (p : Square) (h : p.1 1 ≤ p.1 0) :
    tile 5 p = ![1 - p.1 1, (p.1 0 + p.1 1) / 2 - 1] := by
  rw [tile_of_ge 5 p h]
  have hadd : (5 : Fin 6) + 1 = 0 := by decide
  have hindex : (0 : Fin 6) - 1 = 5 := by decide
  rw [hadd, midpoint, hindex, vertex_five, vertex_zero]
  ext k
  fin_cases k <;> norm_num <;> ring

theorem eq_cornerOne_iff (p : Square) : p = cornerOne ↔ p.1 0 = 1 ∧ p.1 1 = 1 := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, h1⟩
    apply Subtype.ext
    ext k
    fin_cases k <;> assumption

theorem tile_zero_eq_one_iff (p q : Square) :
    tile 0 p = tile 1 q ↔ p.1 0 = 1 ∧ q.1 1 = 1 ∧ q.1 0 = p.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
      first | rw [tile_one_le q hq] at h | rw [tile_one_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hqp⟩
    have hp' : p.1 1 ≤ p.1 0 := by simpa only [hp] using (p.property 1).2
    have hq' : q.1 0 ≤ q.1 1 := by simpa only [hq] using (q.property 0).2
    rw [tile_zero_ge p hp', tile_one_le q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hqp] <;> ring

theorem tile_zero_eq_five_iff (p q : Square) :
    tile 0 p = tile 5 q ↔ p.1 1 = 1 ∧ q.1 0 = 1 ∧ p.1 0 = q.1 1 := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
      first | rw [tile_five_le q hq] at h | rw [tile_five_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨?_, ?_, ?_⟩ <;> linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨hp, hq, hpq⟩
    have hp' : p.1 0 ≤ p.1 1 := by simpa only [hp] using (p.property 0).2
    have hq' : q.1 1 ≤ q.1 0 := by simpa only [hq] using (q.property 1).2
    rw [tile_zero_le p hp', tile_five_ge q hq']
    ext k
    fin_cases k <;> simp [hp, hq, hpq] <;> ring

theorem tile_zero_eq_two_iff (p q : Square) :
    tile 0 p = tile 2 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
      first | rw [tile_two_le q hq] at h | rw [tile_two_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem tile_zero_eq_three_iff (p q : Square) :
    tile 0 p = tile 3 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
      first | rw [tile_three_le q hq] at h | rw [tile_three_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem tile_zero_eq_four_iff (p q : Square) :
    tile 0 p = tile 4 q ↔ p = cornerOne ∧ q = cornerOne := by
  constructor
  · intro h
    have hp0 := (p.property 0).2
    have hp1 := (p.property 1).2
    have hq0 := (q.property 0).2
    have hq1 := (q.property 1).2
    rw [eq_cornerOne_iff, eq_cornerOne_iff]
    rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
      rcases le_total (q.1 0) (q.1 1) with hq | hq
    all_goals
      first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
      first | rw [tile_four_le q hq] at h | rw [tile_four_ge q hq] at h
      have hx := congrFun h 0
      have hy := congrFun h 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        linarith only [hp, hq, hx, hy, hp0, hp1, hq0, hq1]
  · rintro ⟨rfl, rfl⟩
    simp

theorem tile_zero_injective : Function.Injective (tile 0) := by
  intro p q h
  apply Subtype.ext
  rcases le_total (p.1 0) (p.1 1) with hp | hp <;>
    rcases le_total (q.1 0) (q.1 1) with hq | hq
  all_goals
    first | rw [tile_zero_le p hp] at h | rw [tile_zero_ge p hp] at h
    first | rw [tile_zero_le q hq] at h | rw [tile_zero_ge q hq] at h
    have hx := congrFun h 0
    have hy := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
    ext k
    fin_cases k
    · change p.1 0 = q.1 0
      linarith only [hp, hq, hx, hy]
    · change p.1 1 = q.1 1
      linarith only [hp, hq, hx, hy]

open Fin.NatCast

theorem rotate_iterate_tile (n : ℕ) (i : Fin 6) (p : Square) :
    (rotate : Plane → Plane)^[n] (tile i p) = tile (i + (n : Fin 6)) p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, rotate_tile]
    congr 1
    simp only [Nat.cast_succ, add_assoc]

theorem tile_eq_iff_sub (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ tile 0 p = tile (j - i) q := by
  have hp : (rotate : Plane → Plane)^[i.val] (tile 0 p) = tile i p := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, zero_add]
  have hq : (rotate : Plane → Plane)^[i.val] (tile (j - i) q) = tile j q := by
    rw [rotate_iterate_tile]
    simp only [Fin.cast_val_eq_self, sub_add_cancel]
  rw [← hp, ← hq]
  exact (rotate.injective.iterate i.val).eq_iff

theorem squareRel_sub (i j : Fin 6) (p q : Square) :
    SquareRel 0 (j - i) p q ↔ SquareRel i j p q := by
  have h0 : (0 : Fin 6) = j - i ↔ i = j := by
    rw [eq_sub_iff_add_eq, zero_add]
  have h1 : j - i = (0 : Fin 6) + 1 ↔ j = i + 1 := by
    rw [zero_add, sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  have h2 : (0 : Fin 6) = (j - i) + 1 ↔ i = j + 1 := by
    have he : j - i + 1 = (j + 1) - i := by abel
    rw [he, eq_sub_iff_add_eq, zero_add]
  simp only [SquareRel, h0, h1, h2]

theorem eq_cornerOne_iff_all (p : Square) : p = cornerOne ↔ ∀ k, p.1 k = 1 := by
  constructor
  · rintro rfl
    exact fun _ => rfl
  · intro hp
    exact square_eq_of_all_one p cornerOne hp (fun _ => rfl)

theorem tile_zero_eq_iff (j : Fin 6) (p q : Square) :
    tile 0 p = tile j q ↔ SquareRel 0 j p q := by
  fin_cases j
  · change tile 0 p = tile 0 q ↔ SquareRel 0 0 p q
    rw [squareRel_self]
    exact tile_zero_injective.eq_iff
  · change tile 0 p = tile 1 q ↔ SquareRel 0 (0 + 1) p q
    rw [squareRel_next]
    exact tile_zero_eq_one_iff p q
  · change tile 0 p = tile 2 q ↔ SquareRel 0 (0 + 2) p q
    rw [squareRel_add_two, tile_zero_eq_two_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 3 q ↔ SquareRel 0 (0 + 3) p q
    rw [squareRel_add_three, tile_zero_eq_three_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 4 q ↔ SquareRel 0 (0 + 4) p q
    rw [squareRel_add_four, tile_zero_eq_four_iff, eq_cornerOne_iff_all, eq_cornerOne_iff_all]
  · change tile 0 p = tile 5 q ↔ SquareRel 0 (0 + 5) p q
    rw [squareRel_prev, tile_zero_eq_five_iff]
    constructor <;> rintro ⟨h0, h1, h2⟩
    · exact ⟨h0, h1, h2.symm⟩
    · exact ⟨h0, h1, h2.symm⟩

/-- The piecewise-linear tiles have exactly the common square relation
of the oriented toric charts. -/
theorem tile_eq_iff (i j : Fin 6) (p q : Square) :
    tile i p = tile j q ↔ SquareRel i j p q :=
  (tile_eq_iff_sub i j p q).trans
    ((tile_zero_eq_iff (j - i) p q).trans (squareRel_sub i j p q))

theorem tile_injective (i : Fin 6) : Function.Injective (tile i) := by
  intro p q h
  exact (squareRel_self i p q).mp ((tile_eq_iff i i p q).mp h)

theorem tile_sector_of_le (i : Fin 6) (p : Square) (hp : p.1 0 ≤ p.1 1) :
    tile i p = ((p.1 1 - p.1 0) / 2) • vertex (i - 1) +
      (1 - (p.1 0 + p.1 1) / 2) • vertex ((i - 1) + 1) := by
  rw [tile_of_le i p hp, midpoint, sub_add_cancel]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tile_sector_of_ge (i : Fin 6) (p : Square) (hp : p.1 1 ≤ p.1 0) :
    tile i p = (1 - (p.1 0 + p.1 1) / 2) • vertex i +
      ((p.1 0 - p.1 1) / 2) • vertex (i + 1) := by
  rw [tile_of_ge i p hp, midpoint, add_sub_cancel_right]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tile_mem_hexagon (i : Fin 6) (p : Square) : tile i p ∈ Hexagon := by
  have hp0 := p.2 0
  have hp1 := p.2 1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_sector_of_le i p hp]
    apply sector_mem_hexagon (i - 1) <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]
  · rw [tile_sector_of_ge i p hp]
    apply sector_mem_hexagon i <;> linarith [hp0.1, hp0.2, hp1.1, hp1.2]

theorem exists_tile_of_sector (i : Fin 6) (α β : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β ≤ 1) :
    ∃ j : Fin 6, ∃ p : Square, tile j p = α • vertex i + β • vertex (i + 1) := by
  rcases le_total β α with h | h
  · let p : Square := ⟨![1 - α + β, 1 - α - β], by
      intro k
      fin_cases k
      · change 0 ≤ 1 - α + β ∧ 1 - α + β ≤ 1
        constructor <;> linarith
      · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
        constructor <;> linarith⟩
    have hp : p.1 1 ≤ p.1 0 := by
      change 1 - α - β ≤ 1 - α + β
      linarith
    refine ⟨i, p, ?_⟩
    rw [tile_sector_of_ge i p hp]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  · let p : Square := ⟨![1 - α - β, 1 + α - β], by
      intro k
      fin_cases k
      · change 0 ≤ 1 - α - β ∧ 1 - α - β ≤ 1
        constructor <;> linarith
      · change 0 ≤ 1 + α - β ∧ 1 + α - β ≤ 1
        constructor <;> linarith⟩
    have hp : p.1 0 ≤ p.1 1 := by
      change 1 - α - β ≤ 1 + α - β
      linarith
    refine ⟨i + 1, p, ?_⟩
    rw [tile_sector_of_le (i + 1) p hp, add_sub_cancel_right]
    ext k
    simp only [p, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    ring

/-- Every point of the literal hexagonal region lies in one of the six
explicit square tiles. -/
theorem tile_jointly_surjective (x : Hexagon) :
    ∃ i : Fin 6, ∃ p : Square, tile i p = x.val := by
  obtain ⟨i, α, β, hα, hβ, hαβ, hx⟩ := sector_decomposition x.2
  obtain ⟨j, p, hp⟩ := exists_tile_of_sector i α β hα hβ hαβ
  exact ⟨j, p, hp.trans hx.symm⟩

theorem tile_zero_side_zero_eq_one_iff (p : Square) :
    sideFunctional 0 (tile 0 p) = 1 ↔ p.1 0 = 0 := by
  rw [sideFunctional_zero]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

theorem tile_zero_side_one_eq_one_iff (p : Square) :
    sideFunctional 1 (tile 0 p) = 1 ↔ p.1 1 = 0 := by
  rw [sideFunctional_one]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> intro h <;> linarith only [hp, hp0, hp1, h]

theorem tile_zero_side_two_lt_one (p : Square) : sideFunctional 2 (tile 0 p) < 1 := by
  rw [sideFunctional_two]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).1
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem tile_zero_side_three_lt_one (p : Square) : sideFunctional 3 (tile 0 p) < 1 := by
  rw [sideFunctional_three]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem tile_zero_side_four_lt_one (p : Square) : sideFunctional 4 (tile 0 p) < 1 := by
  rw [sideFunctional_four]
  have hp0 := (p.property 0).2
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith only [hp0, hp1]

theorem tile_zero_side_five_lt_one (p : Square) : sideFunctional 5 (tile 0 p) < 1 := by
  rw [sideFunctional_five]
  have hp0 := (p.property 0).1
  have hp1 := (p.property 1).2
  rcases le_total (p.1 0) (p.1 1) with hp | hp
  · rw [tile_zero_le p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]
  · rw [tile_zero_ge p hp]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    linarith only [hp0, hp1]

theorem tile_zero_side_eq_one_iff (p : Square) (k : Fin 6) :
    sideFunctional k (tile 0 p) = 1 ↔
      (k = 0 ∧ p.1 0 = 0) ∨ (k = 1 ∧ p.1 1 = 0) := by
  fin_cases k
  · simpa only [Fin.zero_eta, true_and, or_false,
      show (0 : Fin 6) = 0 ↔ True from iff_true_intro rfl,
      show (0 : Fin 6) = 1 ↔ False from iff_false_intro (by decide), false_and] using
      tile_zero_side_zero_eq_one_iff p
  · simpa only [Fin.mk_one, false_and, false_or, true_and,
      show (1 : Fin 6) = 0 ↔ False from iff_false_intro (by decide),
      show (1 : Fin 6) = 1 ↔ True from iff_true_intro rfl] using
      tile_zero_side_one_eq_one_iff p
  · constructor
    · intro h
      exact ((tile_zero_side_two_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (2 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (2 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_three_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (3 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (3 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_four_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (4 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (4 : Fin 6) ≠ 1 by decide) h).elim
  · constructor
    · intro h
      exact ((tile_zero_side_five_lt_one p).ne h).elim
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact ((show (5 : Fin 6) ≠ 0 by decide) h).elim
      · exact ((show (5 : Fin 6) ≠ 1 by decide) h).elim

/-- Rotation carries each side's supporting function to the next one. -/
theorem sideFunctional_rotate (k : Fin 6) (x : Plane) :
    sideFunctional (k + 1) (rotate x) = sideFunctional k x := by
  fin_cases k
  · change -x 1 + (x 0 + x 1) = x 0
    ring
  · change x 0 + x 1 = x 0 + x 1
    rfl
  · change -(-x 1) = x 1
    ring
  · change -(-x 1) - (x 0 + x 1) = -x 0
    ring
  · change -(x 0 + x 1) = -x 0 - x 1
    ring
  · change -x 1 = -x 1
    rfl

theorem sideFunctional_iterate (n : ℕ) (k : Fin 6) (x : Plane) :
    sideFunctional (k + (n : Fin 6)) ((rotate : Plane → Plane)^[n] x) =
      sideFunctional k x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Function.iterate_succ_apply', sideFunctional_rotate, ih]

theorem sideFunctional_tile_sub (i k : Fin 6) (p : Square) :
    sideFunctional k (tile i p) = sideFunctional (k - i) (tile 0 p) := by
  have h := sideFunctional_iterate i.val (k - i) (tile 0 p)
  simpa only [rotate_iterate_tile, Fin.cast_val_eq_self, sub_add_cancel, zero_add] using h

/-- The two outer edges of each square are exactly the two corresponding
boundary half-edges of the hexagon. -/
theorem tile_mem_side_iff (i k : Fin 6) (p : Square) :
    tile i p ∈ side k ↔
      (k = i ∧ p.1 0 = 0) ∨ (k = i + 1 ∧ p.1 1 = 0) := by
  have h1 : k - i = (1 : Fin 6) ↔ k = i + 1 := by
    rw [sub_eq_iff_eq_add, add_comm (1 : Fin 6) i]
  change (tile i p ∈ Hexagon ∧ sideFunctional k (tile i p) = 1) ↔ _
  rw [sideFunctional_tile_sub]
  simp only [tile_mem_hexagon i p, true_and, tile_zero_side_eq_one_iff, sub_eq_zero, h1]

theorem tile_joint_continuous :
    Continuous (fun p : Fin 6 × Square => tile p.1 p.2) :=
  continuous_prod_of_discrete_left.mpr tile_continuous

end Wikipedia.HopfProblem.CuspHoneycombHexagon
