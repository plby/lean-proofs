import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleSubdivision

/-!
# The upper triangle's actual orientation sign in the second homotopy group

Reversing the second coordinate of the negatively oriented upper triangle
gives the same class as the positively oriented upper triangle. A literal
linear homotopy proves this before the native inverse law is used.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

def subdivisionUpperNegativeMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![min (u 0) (u 1), u 0]
  continuous_toFun := by fun_prop

def subdivisionUpperNegativeReversedMap : C(SubdivisionSquare, SubdivisionSquare) where
  toFun u := ![min (u 0) (σ (u 1)), u 0]
  continuous_toFun := by fun_prop

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem subdivisionUpperNegativeMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeMap, h])⟩
  · exact subdivisionOnDiagonal p hd _
      (by simp [subdivisionUpperNegativeMap, h,
        min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)])

theorem subdivisionUpperNegativeReversedMap_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) : p (subdivisionUpperNegativeReversedMap u) = x := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact p.property _ ⟨1, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact p.property _ ⟨1, Or.inr (by simp [subdivisionUpperNegativeReversedMap, h])⟩
  · exact subdivisionOnDiagonal p hd _
      (by simp [subdivisionUpperNegativeReversedMap, h,
        min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)])
  · exact p.property _ ⟨0, Or.inl (by simp [subdivisionUpperNegativeReversedMap, h])⟩

def subdivisionUpperNegativeLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeMap (subdivisionUpperNegativeMap_based p hd)

def subdivisionUpperNegativeReversedLoop (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) : GenLoop (Fin 2) X x :=
  subdivisionPullbackLoop p subdivisionUpperNegativeReversedMap
    (subdivisionUpperNegativeReversedMap_based p hd)

theorem subdivisionUpperOrientation_sides (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    SubdivisionSameSide (subdivisionUpperTriangleMap u)
      (subdivisionUpperNegativeReversedMap u) := by
  rcases subdivisionSquare_boundary_cases u hu with h | h | h | h
  · exact .zero 1 (by simp [subdivisionUpperTriangleMap, h])
      (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact .one 1 (by simp [subdivisionUpperTriangleMap, h])
      (by simp [subdivisionUpperNegativeReversedMap, h])
  · exact .diagonal (by simp [subdivisionUpperTriangleMap, h])
      (by simp [subdivisionUpperNegativeReversedMap, h,
        min_eq_left (show u 0 ≤ (1 : I) from (u 0).property.2)])
  · exact .zero 0 (by simp [subdivisionUpperTriangleMap, h])
      (by simp [subdivisionUpperNegativeReversedMap, h])

/-- The actual relative homotopy between the two oriented parametrizations. -/
def subdivisionUpperOrientationHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (subdivisionUpperTriangleLoop p hd).val.HomotopyRel
      (subdivisionUpperNegativeReversedLoop p hd).val (Cube.boundary (Fin 2)) :=
  subdivisionLinearHomotopy p hd _ _ (subdivisionUpperTriangleMap_based p hd)
    (subdivisionUpperNegativeReversedMap_based p hd) subdivisionUpperOrientation_sides

theorem subdivisionUpperNegativeReversedLoop_eq_symmAt (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    subdivisionUpperNegativeReversedLoop p hd =
      GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd) := by
  apply GenLoop.ext
  intro u
  change p ![min (u 0) (σ (u 1)), u 0] =
    subdivisionUpperNegativeLoop p hd (fun j => if j = 1 then σ (u 1) else u j)
  simp [subdivisionUpperNegativeLoop, subdivisionPullbackLoop, subdivisionUpperNegativeMap]

theorem subdivisionUpperOrientation_homotopic (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    GenLoop.Homotopic (subdivisionUpperTriangleLoop p hd)
      (GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)) := by
  rw [← subdivisionUpperNegativeReversedLoop_eq_symmAt]
  exact ⟨subdivisionUpperOrientationHomotopy p hd⟩

/-- The sign is the inverse operation of the original homotopy group. -/
theorem subdivisionUpperOrientation_class (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((·⁻¹) : π_ 2 X x → π_ 2 X x) ⟦subdivisionUpperNegativeLoop p hd⟧ := by
  have h : (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      (⟦GenLoop.symmAt (1 : Fin 2) (subdivisionUpperNegativeLoop p hd)⟧ : π_ 2 X x) :=
    Quotient.sound (subdivisionUpperOrientation_homotopic p hd)
  exact h.trans (HomotopyGroup.inv_spec (i := (1 : Fin 2))
    (p := subdivisionUpperNegativeLoop p hd)).symm

theorem subdivisionUpperOrientation_additiveClass (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    Additive.ofMul (⟦subdivisionUpperTriangleLoop p hd⟧ : π_ 2 X x) =
      ((- ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  congrArg Additive.ofMul (subdivisionUpperOrientation_class p hd)

theorem subdivision_eq_sub_of_eq_add {A : Type*} [AddGroup A] {a b c d : A}
    (h : a = b + c) (hc : c = -d) : a = b - d :=
  h.trans ((congrArg (fun z => b + z) hc).trans (sub_eq_add_neg b d).symm)

/-- Diagonal subdivision with the signs of the original singular square chain. -/
theorem subdivision_additiveClass_sub (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) :
    Additive.ofMul (⟦p⟧ : π_ 2 X x) =
      ((· - ·) : Additive (π_ 2 X x) → Additive (π_ 2 X x) → Additive (π_ 2 X x))
        (Additive.ofMul (⟦subdivisionLowerTriangleLoop p hd⟧ : π_ 2 X x))
        (Additive.ofMul (⟦subdivisionUpperNegativeLoop p hd⟧ : π_ 2 X x)) :=
  subdivision_eq_sub_of_eq_add (A := Additive (π_ 2 X x))
    (subdivision_additiveClass p hd) (subdivisionUpperOrientation_additiveClass p hd)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
