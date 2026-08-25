import StackExchange.Puzzling139335.ThreeCorners.FullCorners

/-!
# The intrinsic bisector and center associated with a full square corner

The two short coordinate rays in a full corner neighborhood determine the
outward support bisector.  Consequently this bisector does not depend on a
choice of supporting normals or on the square placement witnessing the corner.
-/

open Set Metric

namespace Puzzling139335.UnitPairs

private theorem bisector_map {P : Set Plane} {a : Plane} (h : SupportCorner P a)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    (h.map e).bisector = e.linearIsometryEquiv h.bisector := by
  simp only [SupportCorner.bisector, SupportCorner.map, map_add]

/-- A full first-quadrant neighborhood at the origin forces the outward
support bisector to have both coordinates equal to minus one. -/
theorem bisector_eq_of_origin_neighborhood {P : Set Plane} {a : Plane}
    (h : SupportCorner P a) (ha : a = 0) {ε : ℝ} (hε : 0 < ε)
    (hnear : ball 0 ε ∩ unitSquare ⊆ P) :
    h.bisector = (!₂[-1, -1] : Plane) := by
  subst a
  let t := min (ε / 2) (1 / 2 : ℝ)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hxnorm : ‖(!₂[t, 0] : Plane)‖ = t := by
    apply (sq_eq_sq₀ (norm_nonneg _) ht.le).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hynorm : ‖(!₂[0, t] : Plane)‖ = t := by
    apply (sq_eq_sq₀ (norm_nonneg _) ht.le).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hx : (!₂[t, 0] : Plane) ∈ P := by
    apply hnear
    constructor
    · exact mem_ball.mpr (by rw [dist_zero_right, hxnorm]; exact htε)
    · simpa [unitSquare] using And.intro ht.le ht1
  have hy : (!₂[0, t] : Plane) ∈ P := by
    apply hnear
    constructor
    · exact mem_ball.mpr (by rw [dist_zero_right, hynorm]; exact htε)
    · simpa [unitSquare] using And.intro ht.le ht1
  have hxproj := h.bisector_projection hx
  have hyproj := h.bisector_projection hy
  simp only [sub_zero, Schoenflies.Plane.inner_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, add_zero, zero_add, hxnorm, hynorm] at hxproj hyproj
  have hxle : h.bisector 0 ≤ -1 :=
    le_of_mul_le_mul_right (by simpa only [neg_one_mul] using hxproj) ht
  have hyle : h.bisector 1 ≤ -1 :=
    le_of_mul_le_mul_right (by simpa only [neg_one_mul] using hyproj) ht
  have hsq : h.bisector 0 ^ 2 + h.bisector 1 ^ 2 = 2 := by
    simpa only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] using h.bisector_norm_sq
  have hxval : h.bisector 0 = -1 := by
    nlinarith [sq_nonneg (h.bisector 0 + 1), sq_nonneg (h.bisector 1 + 1)]
  have hyval : h.bisector 1 = -1 := by
    nlinarith [sq_nonneg (h.bisector 0 + 1), sq_nonneg (h.bisector 1 + 1)]
  ext i
  fin_cases i
  · exact hxval
  · exact hyval

/-- A full square corner has a unique outward support bisector, although
the two supporting normals can be interchanged. -/
theorem IsFullSquareCorner.bisector_eq {P : Set Plane} {a : Plane}
    (hfull : IsFullSquareCorner P a) (h k : SupportCorner P a) :
    h.bisector = k.bisector := by
  obtain ⟨f, hfa, _, ε, hε, hnear⟩ := hfull.exists_normalized
  apply f.linearIsometryEquiv.injective
  calc
    f.linearIsometryEquiv h.bisector = (h.map f).bisector := (bisector_map h f).symm
    _ = (!₂[-1, -1] : Plane) :=
      bisector_eq_of_origin_neighborhood (h.map f) hfa hε hnear
    _ = (k.map f).bisector :=
      (bisector_eq_of_origin_neighborhood (k.map f) hfa hε hnear).symm
    _ = f.linearIsometryEquiv k.bisector := bisector_map k f

/-- Every placement taking a full corner to a square vertex carries its
intrinsic bisector to the canonical bisector at that vertex. -/
theorem IsFullSquareCorner.map_bisector_eq_square {P : Set Plane} {a : Plane}
    (hfull : IsFullSquareCorner P a) (h : SupportCorner P a)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (j : Fin 4)
    (hsub : e '' P ⊆ unitSquare) (hea : e a = corner j) :
    e.linearIsometryEquiv h.bisector = (squareSupportCorner j).bisector := by
  let k : SupportCorner (e '' P) (e a) :=
    { mem := mem_image_of_mem e h.mem
      firstNormal := (squareSupportCorner j).firstNormal
      secondNormal := (squareSupportCorner j).secondNormal
      norm_firstNormal := (squareSupportCorner j).norm_firstNormal
      norm_secondNormal := (squareSupportCorner j).norm_secondNormal
      orthogonal := (squareSupportCorner j).orthogonal
      first_support := by
        intro x hx
        rw [hea]
        exact (squareSupportCorner j).first_support x (hsub hx)
      second_support := by
        intro x hx
        rw [hea]
        exact (squareSupportCorner j).second_support x (hsub hx) }
  calc
    e.linearIsometryEquiv h.bisector = (h.map e).bisector := (bisector_map h e).symm
    _ = k.bisector := (hfull.map e).bisector_eq (h.map e) k
    _ = (squareSupportCorner j).bisector := rfl

private theorem squareCenter_sub_corner_eq_neg_half_bisector (j : Fin 4) :
    squareCenter - corner j = -(1 / 2 : ℝ) • (squareSupportCorner j).bisector := by
  fin_cases j <;> ext k <;> fin_cases k <;>
    norm_num [squareCenter, corner, squareSupportCorner, SupportCorner.bisector,
      Fin.ext_iff]

/-- The square center pulled back through any actual placement at a full
corner is determined by that corner and its intrinsic outward bisector. -/
theorem IsFullSquareCorner.symm_center_eq {P : Set Plane} {a : Plane}
    (hfull : IsFullSquareCorner P a) (h : SupportCorner P a)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (j : Fin 4)
    (hsub : e '' P ⊆ unitSquare) (hea : e a = corner j) :
    e.symm squareCenter = a - (1 / 2 : ℝ) • h.bisector := by
  have heh := hfull.map_bisector_eq_square h e j hsub hea
  have hdiff : e.symm squareCenter - a = -(1 / 2 : ℝ) • h.bisector := by
    apply e.linearIsometryEquiv.injective
    have hmap : e.linearIsometryEquiv (e.symm squareCenter - a) =
        e (e.symm squareCenter) - e a := e.map_vsub _ _
    rw [hmap, e.apply_symm_apply, hea, map_smul, heh]
    exact squareCenter_sub_corner_eq_neg_half_bisector j
  calc
    e.symm squareCenter = -(1 / 2 : ℝ) • h.bisector + a :=
      sub_eq_iff_eq_add.mp hdiff
    _ = a - (1 / 2 : ℝ) • h.bisector := by
      simp [sub_eq_add_neg, add_comm]

end Puzzling139335.UnitPairs
