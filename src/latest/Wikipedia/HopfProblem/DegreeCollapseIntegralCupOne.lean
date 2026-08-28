import Wikipedia.HopfProblem.DegreeCollapseIntegralCupOneFaces

/-!
# The signed integral cup-one identity in degrees four and three

The four overlapping-face summands are evaluated on the original
singular simplex. The degree-seven differential identity keeps both
coboundary terms; it is not restricted to closed inputs.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne

open FirstHurewicz SingularCohomologyCup

variable {X : Type} [TopologicalSpace X]

def value43 (α : Cochain X 4) (β : Cochain X 3) (σ : SingularSimplex X 6) : ℤ :=
  faceValue α σ ![0, 3, 4, 5, 6] * faceValue β σ ![0, 1, 2, 3] +
  faceValue α σ ![0, 1, 4, 5, 6] * faceValue β σ ![1, 2, 3, 4] +
  faceValue α σ ![0, 1, 2, 5, 6] * faceValue β σ ![2, 3, 4, 5] +
  faceValue α σ ![0, 1, 2, 3, 6] * faceValue β σ ![3, 4, 5, 6]

def value44 (α : Cochain X 4) (β : Cochain X 4) (σ : SingularSimplex X 7) : ℤ :=
  faceValue α σ ![0, 4, 5, 6, 7] * faceValue β σ ![0, 1, 2, 3, 4] -
  faceValue α σ ![0, 1, 5, 6, 7] * faceValue β σ ![1, 2, 3, 4, 5] +
  faceValue α σ ![0, 1, 2, 6, 7] * faceValue β σ ![2, 3, 4, 5, 6] -
  faceValue α σ ![0, 1, 2, 3, 7] * faceValue β σ ![3, 4, 5, 6, 7]

def value53 (α : Cochain X 5) (β : Cochain X 3) (σ : SingularSimplex X 7) : ℤ :=
  faceValue α σ ![0, 3, 4, 5, 6, 7] * faceValue β σ ![0, 1, 2, 3] +
  faceValue α σ ![0, 1, 4, 5, 6, 7] * faceValue β σ ![1, 2, 3, 4] +
  faceValue α σ ![0, 1, 2, 5, 6, 7] * faceValue β σ ![2, 3, 4, 5] +
  faceValue α σ ![0, 1, 2, 3, 6, 7] * faceValue β σ ![3, 4, 5, 6] +
  faceValue α σ ![0, 1, 2, 3, 4, 7] * faceValue β σ ![4, 5, 6, 7]

def cupOne43 (α : Cochain X 4) (β : Cochain X 3) : Cochain X 6 :=
  chainLift X 6 (value43 α β)

def cupOne44 (α : Cochain X 4) (β : Cochain X 4) : Cochain X 7 :=
  chainLift X 7 (value44 α β)

def cupOne53 (α : Cochain X 5) (β : Cochain X 3) : Cochain X 7 :=
  chainLift X 7 (value53 α β)

theorem cupOne43_simplex (α : Cochain X 4) (β : Cochain X 3) (σ : SingularSimplex X 6) :
    cupOne43 α β (simplexChain X 6 σ) = value43 α β σ := chainLift_simplex X 6 _ σ

theorem cupOne44_simplex (α : Cochain X 4) (β : Cochain X 4) (σ : SingularSimplex X 7) :
    cupOne44 α β (simplexChain X 7 σ) = value44 α β σ := chainLift_simplex X 7 _ σ

theorem cupOne53_simplex (α : Cochain X 5) (β : Cochain X 3) (σ : SingularSimplex X 7) :
    cupOne53 α β (simplexChain X 7 σ) = value53 α β σ := chainLift_simplex X 7 _ σ

theorem value43_comp {n : ℕ} (α : Cochain X 4) (β : Cochain X 3)
    (σ : SingularSimplex X n) (v : Fin 7 → Fin (n + 1)) :
    value43 α β (σ.comp (vertexMap v)) =
      faceValue α σ ![v 0, v 3, v 4, v 5, v 6] * faceValue β σ ![v 0, v 1, v 2, v 3] +
      faceValue α σ ![v 0, v 1, v 4, v 5, v 6] * faceValue β σ ![v 1, v 2, v 3, v 4] +
      faceValue α σ ![v 0, v 1, v 2, v 5, v 6] * faceValue β σ ![v 2, v 3, v 4, v 5] +
      faceValue α σ ![v 0, v 1, v 2, v 3, v 6] * faceValue β σ ![v 3, v 4, v 5, v 6] := by
  simp only [value43, faceValue_comp, comp_vecCons, comp_vecEmpty]

theorem cup43_simplex (α : Cochain X 4) (β : Cochain X 3) (σ : SingularSimplex X 7) :
    cup α β (simplexChain X 7 σ) =
      faceValue α σ ![0, 1, 2, 3, 4] * faceValue β σ ![4, 5, 6, 7] := by
  have hf : frontFace 4 3 = vertexMap ![0, 1, 2, 3, 4] := by
    apply congrArg vertexMap
    funext i
    fin_cases i <;> rfl
  have hb : backFace 4 3 = vertexMap ![4, 5, 6, 7] := by
    apply congrArg vertexMap
    funext i
    fin_cases i <;> rfl
  rw [cup_simplex, hf, hb]
  rfl

theorem cup34_simplex (α : Cochain X 3) (β : Cochain X 4) (σ : SingularSimplex X 7) :
    cup α β (simplexChain X 7 σ) =
      faceValue α σ ![0, 1, 2, 3] * faceValue β σ ![3, 4, 5, 6, 7] := by
  have hf : frontFace 3 4 = vertexMap ![0, 1, 2, 3] := by
    apply congrArg vertexMap
    funext i
    fin_cases i <;> rfl
  have hb : backFace 3 4 = vertexMap ![3, 4, 5, 6, 7] := by
    apply congrArg vertexMap
    funext i
    fin_cases i <;> rfl
  rw [cup_simplex, hf, hb]
  rfl

theorem coboundary_cupOne43 (α : Cochain X 4) (β : Cochain X 3) :
    coboundary (cupOne43 α β) = cupOne53 (coboundary α) β +
      cupOne44 α (coboundary β) + cup α β - cup β α := by
  apply chainMap_ext X 7
  intro σ
  simp only [coboundary_simplex, Fin.sum_univ_succ, Fin.sum_univ_zero,
    cupOne43_simplex, simplexFace_six, value43_comp,
    LinearMap.add_apply, LinearMap.sub_apply, cupOne53_simplex, cupOne44_simplex,
    cup43_simplex, cup34_simplex, value53, value44,
    coboundary_faceValue_three, coboundary_faceValue_four]
  norm_num [Matrix.cons_val]
  dsimp only [Matrix.cons_val]
  dsimp only [Matrix.cons_val]
  ring

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne
