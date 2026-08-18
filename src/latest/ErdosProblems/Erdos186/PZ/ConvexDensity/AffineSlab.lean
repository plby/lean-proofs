import Mathlib

/-!
# Axis boxes and affine slabs in finite-dimensional Euclidean space
-/

open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity.AffineSlab

set_option autoImplicit false

noncomputable section

/-- Euclidean space in its standard coordinate model. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The closed axis-parallel box with the indicated endpoints. -/
def axisBaseBox {d : ℕ} (lower upper : E d) : Set (E d) :=
  {x | ∀ j, lower.ofLp j ≤ x.ofLp j ∧ x.ofLp j ≤ upper.ofLp j}

@[simp]
theorem mem_axisBaseBox_iff {d : ℕ} {lower upper x : E d} :
    x ∈ axisBaseBox lower upper ↔
      ∀ j, lower.ofLp j ≤ x.ofLp j ∧ x.ofLp j ≤ upper.ofLp j := by
  rfl

theorem convex_axisBaseBox {d : ℕ} (lower upper : E d) :
    Convex ℝ (axisBaseBox lower upper) := by
  intro x hx y hy a b ha hb hab j
  have hxj := hx j
  have hyj := hy j
  constructor
  · change lower.ofLp j ≤ a * x.ofLp j + b * y.ofLp j
    calc
      lower.ofLp j = a * lower.ofLp j + b * lower.ofLp j := by
        rw [← add_mul, hab, one_mul]
      _ ≤ a * x.ofLp j + b * y.ofLp j :=
        add_le_add (mul_le_mul_of_nonneg_left hxj.1 ha)
          (mul_le_mul_of_nonneg_left hyj.1 hb)
  · change a * x.ofLp j + b * y.ofLp j ≤ upper.ofLp j
    calc
      a * x.ofLp j + b * y.ofLp j ≤
          a * upper.ofLp j + b * upper.ofLp j :=
        add_le_add (mul_le_mul_of_nonneg_left hxj.2 ha)
          (mul_le_mul_of_nonneg_left hyj.2 hb)
      _ = upper.ofLp j := by rw [← add_mul, hab, one_mul]

theorem measurableSet_axisBaseBox {d : ℕ} (lower upper : E d) :
    MeasurableSet (axisBaseBox lower upper) := by
  rw [show axisBaseBox lower upper =
      ⋂ j, (fun x : E d ↦ x.ofLp j) ⁻¹' Set.Icc (lower.ofLp j) (upper.ofLp j) by
    ext x
    simp [axisBaseBox]]
  exact MeasurableSet.iInter fun j ↦ measurableSet_Icc.preimage
    (PiLp.continuous_apply 2 (fun _ : Fin d ↦ ℝ) j).measurable

/-- Exact Lebesgue volume of a Euclidean axis box. -/
theorem volume_axisBaseBox {d : ℕ} (lower upper : E d) :
    volume (axisBaseBox lower upper) =
      ∏ j : Fin d, ENNReal.ofReal (upper.ofLp j - lower.ofLp j) := by
  have h := (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    (measurableSet_axisBaseBox lower upper).nullMeasurableSet
  have hpre : (WithLp.toLp 2) ⁻¹' axisBaseBox lower upper =
      Set.Icc lower.ofLp upper.ofLp := by
    ext x
    change (∀ j, lower.ofLp j ≤ x j ∧ x j ≤ upper.ofLp j) ↔
      (∀ j, lower.ofLp j ≤ x j) ∧ ∀ j, x j ≤ upper.ofLp j
    aesop
  rw [hpre, Real.volume_Icc_pi] at h
  exact h.symm

/-- Delete coordinate `i`, retaining the remaining coordinates in their `succAbove` order. -/
def eraseCoordinate {d : ℕ} (i : Fin (d + 1)) (x : E (d + 1)) : E d :=
  WithLp.toLp 2 (i.removeNth x.ofLp)

@[simp]
theorem eraseCoordinate_apply {d : ℕ} (i : Fin (d + 1)) (x : E (d + 1)) (j : Fin d) :
    (eraseCoordinate i x).ofLp j = x.ofLp (i.succAbove j) := by
  rfl

/-- Split Euclidean `(d+1)`-space as the remaining `d` coordinates followed by coordinate `i`. -/
def splitCoordinate {d : ℕ} (i : Fin (d + 1)) (x : E (d + 1)) : E d × ℝ :=
  (WithLp.toLp 2 (i.removeNth x.ofLp), x.ofLp i)

/-- Reinsert a distinguished coordinate.  This is the explicit inverse of `splitCoordinate`. -/
def joinCoordinate {d : ℕ} (i : Fin (d + 1)) (p : E d × ℝ) : E (d + 1) :=
  WithLp.toLp 2 (i.insertNth p.2 p.1.ofLp)

@[simp]
theorem eraseCoordinate_joinCoordinate {d : ℕ} (i : Fin (d + 1)) (p : E d × ℝ) :
    eraseCoordinate i (joinCoordinate i p) = p.1 := by
  ext j
  simp [eraseCoordinate, joinCoordinate]

@[simp]
theorem joinCoordinate_apply_same {d : ℕ} (i : Fin (d + 1)) (p : E d × ℝ) :
    (joinCoordinate i p).ofLp i = p.2 := by
  simp [joinCoordinate]

@[simp]
theorem splitCoordinate_joinCoordinate {d : ℕ} (i : Fin (d + 1)) (p : E d × ℝ) :
    splitCoordinate i (joinCoordinate i p) = p := by
  apply Prod.ext
  · exact eraseCoordinate_joinCoordinate i p
  · exact joinCoordinate_apply_same i p

@[simp]
theorem joinCoordinate_splitCoordinate {d : ℕ} (i : Fin (d + 1)) (x : E (d + 1)) :
    joinCoordinate i (splitCoordinate i x) = x := by
  rw [WithLp.ext_iff]
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp [joinCoordinate, splitCoordinate]
  · intro j
    simp [joinCoordinate, splitCoordinate]

/-- The coordinate decomposition is linear. -/
def splitCoordinateLinearMap {d : ℕ} (i : Fin (d + 1)) :
    E (d + 1) →ₗ[ℝ] E d × ℝ where
  toFun := splitCoordinate i
  map_add' x y := by
    ext <;> simp [splitCoordinate, Fin.removeNth]
  map_smul' c x := by
    ext <;> simp [splitCoordinate, Fin.removeNth]

@[simp]
theorem splitCoordinateLinearMap_apply {d : ℕ} (i : Fin (d + 1)) (x : E (d + 1)) :
    splitCoordinateLinearMap i x = splitCoordinate i x := rfl

/-- Splitting off any coordinate preserves Lebesgue volume. -/
theorem measurePreserving_splitCoordinate {d : ℕ} (i : Fin (d + 1)) :
    MeasurePreserving (splitCoordinate i) := by
  change MeasurePreserving
    (fun x : E (d + 1) ↦ (WithLp.toLp 2 (i.removeNth x.ofLp), x.ofLp i))
  let h₁ : MeasurePreserving (@WithLp.ofLp 2 (Fin (d + 1) → ℝ)) :=
    PiLp.volume_preserving_ofLp (Fin (d + 1))
  let h₂ : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) i) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) ↦ ℝ) i
  let h₃ : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (@WithLp.toLp 2 (Fin d → ℝ))) :=
    MeasurePreserving.prod
      (μa := (volume : Measure ℝ)) (μb := (volume : Measure ℝ))
      (μc := (volume : Measure (Fin d → ℝ)))
      (μd := (volume : Measure (E d)))
      (MeasurePreserving.id (volume : Measure ℝ))
      (PiLp.volume_preserving_toLp (Fin d))
  let h₄ : MeasurePreserving (fun p : ℝ × E d ↦ (p.2, p.1)) :=
    Measure.measurePreserving_swap
  have h := h₄.comp (h₃.comp (h₂.comp h₁))
  simpa [Function.comp_def,
    MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv] using h

theorem measurable_splitCoordinate {d : ℕ} (i : Fin (d + 1)) :
    Measurable (splitCoordinate i) :=
  (measurePreserving_splitCoordinate i).measurable

/-- The affine graph height determined by a continuous linear functional and an intercept. -/
def affineValue {d : ℕ} (ell : E d →L[ℝ] ℝ) (offset : ℝ) (y : E d) : ℝ :=
  ell y + offset

/-- The open slab of total thickness `thickness` around an affine graph, cut off over an
axis-parallel base box.  If `thickness ≤ 0`, it is empty. -/
def affineSlab {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) : Set (E (d + 1)) :=
  {x | eraseCoordinate i x ∈ axisBaseBox lower upper ∧
    affineValue ell offset (eraseCoordinate i x) - thickness / 2 < x.ofLp i ∧
    x.ofLp i < affineValue ell offset (eraseCoordinate i x) + thickness / 2}

@[simp]
theorem mem_affineSlab_iff {d : ℕ} {lower upper : E d} {i : Fin (d + 1)}
    {ell : E d →L[ℝ] ℝ} {offset thickness : ℝ} {x : E (d + 1)} :
    x ∈ affineSlab lower upper i ell offset thickness ↔
      eraseCoordinate i x ∈ axisBaseBox lower upper ∧
      affineValue ell offset (eraseCoordinate i x) - thickness / 2 < x.ofLp i ∧
      x.ofLp i < affineValue ell offset (eraseCoordinate i x) + thickness / 2 := by
  rfl

/-- Product-coordinate form of an affine slab. -/
theorem affineSlab_eq_preimage_regionBetween {d : ℕ} (lower upper : E d)
    (i : Fin (d + 1)) (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    affineSlab lower upper i ell offset thickness =
      splitCoordinate i ⁻¹'
        regionBetween
          (fun y ↦ affineValue ell offset y - thickness / 2)
          (fun y ↦ affineValue ell offset y + thickness / 2)
          (axisBaseBox lower upper) := by
  rfl

/-- Subtract the linear part of an affine graph from the distinguished coordinate. -/
def graphDeviationLinearMap {d : ℕ} (ell : E d →L[ℝ] ℝ) :
    E d × ℝ →ₗ[ℝ] E d × ℝ where
  toFun p := (p.1, p.2 - ell p.1)
  map_add' p q := by
    apply Prod.ext
    · simp
    · simp [map_add]
      ring
  map_smul' c p := by
    apply Prod.ext
    · simp
    · simp [map_smul]
      ring

/-- The slab is also the inverse image of a literal product box after subtracting the
linear part of its graph.  This identity is the convexity bridge. -/
theorem affineSlab_eq_linear_preimage {d : ℕ} (lower upper : E d)
    (i : Fin (d + 1)) (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    affineSlab lower upper i ell offset thickness =
      splitCoordinateLinearMap i ⁻¹'
        (graphDeviationLinearMap ell ⁻¹'
          (axisBaseBox lower upper ×ˢ
            Set.Ioo (offset - thickness / 2) (offset + thickness / 2))) := by
  ext x
  simp only [affineSlab, Set.mem_ofPred_eq, Set.mem_preimage,
    splitCoordinateLinearMap_apply, splitCoordinate, eraseCoordinate, graphDeviationLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk, Set.mem_prod, Set.mem_Ioo, affineValue]
  constructor
  · rintro ⟨hx, hlow, hupp⟩
    exact ⟨hx, by linarith, by linarith⟩
  · rintro ⟨hx, hlow, hupp⟩
    exact ⟨hx, by linarith, by linarith⟩

theorem convex_affineSlab {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    Convex ℝ (affineSlab lower upper i ell offset thickness) := by
  rw [affineSlab_eq_linear_preimage]
  exact (((convex_axisBaseBox lower upper).prod
    (convex_Ioo (offset - thickness / 2) (offset + thickness / 2))).linear_preimage
      (graphDeviationLinearMap ell)).linear_preimage (splitCoordinateLinearMap i)

theorem measurableSet_affineSlab {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    MeasurableSet (affineSlab lower upper i ell offset thickness) := by
  rw [affineSlab_eq_preimage_regionBetween]
  apply (measurableSet_regionBetween
    (ell.continuous.measurable.add_const offset |>.sub_const (thickness / 2))
    (ell.continuous.measurable.add_const offset |>.add_const (thickness / 2))
    (measurableSet_axisBaseBox lower upper)).preimage
  exact measurable_splitCoordinate i

/-- Exact slab formula: shearing by an affine functional does not affect volume. -/
theorem volume_affineSlab {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    volume (affineSlab lower upper i ell offset thickness) =
      ENNReal.ofReal thickness * volume (axisBaseBox lower upper) := by
  let f : E d → ℝ := fun y ↦ affineValue ell offset y - thickness / 2
  let g : E d → ℝ := fun y ↦ affineValue ell offset y + thickness / 2
  have hf : Measurable f :=
    ell.continuous.measurable.add_const offset |>.sub_const (thickness / 2)
  have hg : Measurable g :=
    ell.continuous.measurable.add_const offset |>.add_const (thickness / 2)
  rw [affineSlab_eq_preimage_regionBetween]
  change volume (splitCoordinate i ⁻¹' regionBetween f g (axisBaseBox lower upper)) = _
  rw [(measurePreserving_splitCoordinate i).measure_preimage
    (measurableSet_regionBetween hf hg
      (measurableSet_axisBaseBox lower upper)).nullMeasurableSet]
  change (volume : Measure (E d)).prod (volume : Measure ℝ)
    (regionBetween f g (axisBaseBox lower upper)) = _
  rw [volume_regionBetween_eq_lintegral' hf hg
    (measurableSet_axisBaseBox lower upper)]
  have hgf : g - f = fun _ ↦ thickness := by
    funext y
    dsimp [f, g, affineValue]
    ring
  rw [hgf, setLIntegral_const]

/-- Fully coordinate-expanded volume formula. -/
theorem volume_affineSlab_eq_prod {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness : ℝ) :
    volume (affineSlab lower upper i ell offset thickness) =
      ENNReal.ofReal thickness *
        ∏ j : Fin d, ENNReal.ofReal (upper.ofLp j - lower.ofLp j) := by
  rw [volume_affineSlab, volume_axisBaseBox]

/-- A requested ambient thickness gives the corresponding slab-volume upper bound. -/
theorem volume_affineSlab_le {d : ℕ} (lower upper : E d) (i : Fin (d + 1))
    (ell : E d →L[ℝ] ℝ) (offset thickness bound : ℝ) (h : thickness ≤ bound) :
    volume (affineSlab lower upper i ell offset thickness) ≤
      ENNReal.ofReal bound * volume (axisBaseBox lower upper) := by
  rw [volume_affineSlab]
  gcongr

end

end Erdos186.PZ.ConvexDensity.AffineSlab
