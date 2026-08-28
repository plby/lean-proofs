import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivisionBasic

/-!
# The two actual triangular parts of a square

The lower triangle uses vertices `(0,0),(1,0),(1,1)`, and the upper
triangle uses vertices `(0,0),(1,1),(0,1)`. Both parametrizations have
positive orientation. The product and cone parametrizations will provide
explicit relative homotopies to these triangle maps.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

/-- The nonnegative difference between the first parameter and their minimum. -/
def subdivisionSubMin (u v : I) : I :=
  ⟨(u : ℝ) - min (u : ℝ) (v : ℝ),
    sub_nonneg.mpr (min_le_left _ _),
    (sub_le_self _ (le_min u.property.1 v.property.1)).trans u.property.2⟩

@[simp] theorem subdivisionSubMin_coe (u v : I) :
    (subdivisionSubMin u v : ℝ) = (u : ℝ) - min (u : ℝ) (v : ℝ) := rfl

@[simp] theorem subdivisionSubMin_zero_left (v : I) : subdivisionSubMin 0 v = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.1]

@[simp] theorem subdivisionSubMin_zero_right (u : I) : subdivisionSubMin u 0 = u := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.1]

@[simp] theorem subdivisionSubMin_one_left (v : I) : subdivisionSubMin 1 v = σ v := by
  apply Subtype.ext
  simp [subdivisionSubMin, v.property.2]

@[simp] theorem subdivisionSubMin_one_right (u : I) : subdivisionSubMin u 1 = 0 := by
  apply Subtype.ext
  simp [subdivisionSubMin, u.property.2]

theorem continuous_subdivisionSubMin :
    Continuous fun u : I × I => subdivisionSubMin u.1 u.2 := by
  unfold subdivisionSubMin
  fun_prop

def subdivisionLowerProductMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![u 0, u 0 * u 1]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => u 0 * u 1
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp (continuous_apply 0)).mul
        (continuous_subtype_val.comp (continuous_apply 1))

def subdivisionUpperProductMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![u 0, Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

def subdivisionUpperConeMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![u 0 * σ (u 1), Set.Icc.convexComb (u 0) 1 (u 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => u 0 * σ (u 1)
      apply Continuous.subtype_mk
      change Continuous fun u : SubdivisionSquare => (u 0 : ℝ) * (1 - (u 1 : ℝ))
      fun_prop
    · change Continuous fun u : SubdivisionSquare => Set.Icc.convexComb (u 0) 1 (u 1)
      unfold Set.Icc.convexComb
      fun_prop

/-- The positively oriented lower-triangle quotient of the parameter square. -/
def subdivisionLowerTriangleMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![u 0, min (u 0) (u 1)]
  continuous_toFun := by fun_prop

/-- The positively oriented upper-triangle quotient of the parameter square. -/
def subdivisionUpperTriangleMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![subdivisionSubMin (u 0) (u 1), u 0]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous fun u : SubdivisionSquare => subdivisionSubMin (u 0) (u 1)
      unfold subdivisionSubMin
      fun_prop
    · exact continuous_apply 0

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem subdivisionLowerProductMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerProductMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionLowerProductMap, h])

theorem subdivisionUpperProductMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperProductMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperProductMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionUpperProductMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperProductMap, h])
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperProductMap, h])⟩

theorem subdivisionUpperConeMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperConeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperConeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperConeMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperConeMap, h])⟩

theorem subdivisionLowerTriangleMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionLowerTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨0, Or.inr (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionLowerTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _
      (by simp [subdivisionLowerTriangleMap, h,
        min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)])

theorem subdivisionUpperTriangleMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperTriangleMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperTriangleMap, h])⟩
  · exact subdivisionOnDiagonal p hd _ (by simp [subdivisionUpperTriangleMap, h])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperTriangleMap, h])⟩

def subdivisionLowerProductLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerProductMap (subdivisionLowerProductMap_based p hd)

def subdivisionUpperProductLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperProductMap (subdivisionUpperProductMap_based p hd)

def subdivisionUpperConeLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperConeMap (subdivisionUpperConeMap_based p hd)

def subdivisionLowerTriangleLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionLowerTriangleMap (subdivisionLowerTriangleMap_based p hd)

def subdivisionUpperTriangleLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperTriangleMap (subdivisionUpperTriangleMap_based p hd)

@[simp] theorem subdivisionLowerTriangleLoop_apply (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare) :
    subdivisionLowerTriangleLoop p hd u = p ![u 0, min (u 0) (u 1)] := rfl

@[simp] theorem subdivisionUpperTriangleLoop_apply (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare) :
    subdivisionUpperTriangleLoop p hd u = p ![subdivisionSubMin (u 0) (u 1), u 0] := rfl

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
