import Wikipedia.HopfProblem.SecondHurewiczNativeMapsLoops
import Mathlib.Tactic.FinCases

/-!
# Linear homotopies of squares with a collapsed diagonal

All homotopies here are homotopies of Mathlib's actual generalized loops,
relative to their entire cube boundary. The only extra geometric condition
is that the original square sends its diagonal to the base point.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

abbrev SubdivisionSquare := Fin 2 → I

theorem subdivisionSquare_boundary_cases (u : SubdivisionSquare)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    u 0 = 0 ∨ u 0 = 1 ∨ u 1 = 0 ∨ u 1 = 1 := by
  rcases hu with ⟨i, hi⟩
  fin_cases i
  · rcases hi with hi | hi
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · rcases hi with hi | hi
    · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr hi))

/-- The two points lie on one common side of the square, or both on its diagonal. -/
inductive SubdivisionSameSide (a b : SubdivisionSquare) : Prop
  | zero (i : Fin 2) (ha : a i = 0) (hb : b i = 0)
  | one (i : Fin 2) (ha : a i = 1) (hb : b i = 1)
  | diagonal (ha : a 0 = a 1) (hb : b 0 = b 1)

/-- Coordinatewise linear interpolation inside the actual cube. -/
def subdivisionBlend (t : I) (a b : SubdivisionSquare) : SubdivisionSquare :=
  fun i => Set.Icc.convexComb (a i) (b i) t

@[simp] theorem subdivisionBlend_zero (a b : SubdivisionSquare) :
    subdivisionBlend 0 a b = a := by
  funext i
  exact Set.Icc.convexComb_zero _ _

@[simp] theorem subdivisionBlend_one (a b : SubdivisionSquare) :
    subdivisionBlend 1 a b = b := by
  funext i
  exact Set.Icc.convexComb_one _ _

def subdivisionBlendMap (f g : C(SubdivisionSquare, SubdivisionSquare)) :
    C(I × SubdivisionSquare, SubdivisionSquare) where
  toFun u := subdivisionBlend u.1 (f u.2) (g u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Set.Icc.continuous_convexComb_prod.comp
      (((continuous_apply i).comp (f.continuous.comp continuous_snd)).prodMk
        (((continuous_apply i).comp (g.continuous.comp continuous_snd)).prodMk
          continuous_fst))

variable {X : Type*} [TopologicalSpace X] {x : X}

theorem subdivisionOnDiagonal (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) (a : SubdivisionSquare)
    (ha : a 0 = a 1) : p a = x := by
  have h : a = ![a 0, a 0] := by
    funext i
    fin_cases i
    · rfl
    · exact ha.symm
  exact (congrArg p h).trans (hd _)

theorem subdivisionBlend_based (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x) {a b : SubdivisionSquare}
    (h : SubdivisionSameSide a b) (t : I) :
    p (subdivisionBlend t a b) = x := by
  cases h with
  | zero i ha hb =>
      apply p.property
      exact ⟨i, Or.inl (by simp [subdivisionBlend, ha, hb])⟩
  | one i ha hb =>
      apply p.property
      exact ⟨i, Or.inr (by simp [subdivisionBlend, ha, hb])⟩
  | diagonal ha hb =>
      apply subdivisionOnDiagonal p hd
      simp only [subdivisionBlend, ha, hb]

/-- A reparametrization whose boundary is sent to the original base point. -/
def subdivisionPullbackLoop (p : GenLoop (Fin 2) X x)
    (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) : GenLoop (Fin 2) X x :=
  ⟨p.val.comp f, hf⟩

@[simp] theorem subdivisionPullbackLoop_apply (p : GenLoop (Fin 2) X x)
    (f : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x) (u : SubdivisionSquare) :
    subdivisionPullbackLoop p f hf u = p (f u) := rfl

/-- The explicit linear homotopy is relative to the entire perimeter whenever
corresponding perimeter points lie on a common side or on the collapsed diagonal. -/
def subdivisionLinearHomotopy (p : GenLoop (Fin 2) X x)
    (hd : ∀ t : I, p ![t, t] = x)
    (f g : C(SubdivisionSquare, SubdivisionSquare))
    (hf : ∀ u ∈ Cube.boundary (Fin 2), p (f u) = x)
    (hg : ∀ u ∈ Cube.boundary (Fin 2), p (g u) = x)
    (hfg : ∀ u ∈ Cube.boundary (Fin 2), SubdivisionSameSide (f u) (g u)) :
    (subdivisionPullbackLoop p f hf).val.HomotopyRel
      (subdivisionPullbackLoop p g hg).val (Cube.boundary (Fin 2)) where
  toFun u := p (subdivisionBlend u.1 (f u.2) (g u.2))
  continuous_toFun := p.val.continuous.comp (subdivisionBlendMap f g).continuous
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' t u hu := (subdivisionBlend_based p hd (hfg u hu) t).trans (hf u hu).symm

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
