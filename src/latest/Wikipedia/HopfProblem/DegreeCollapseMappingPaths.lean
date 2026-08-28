import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.CompactOpen

/-!
# Homotopies as paths in genuine continuous-map spaces

The pointwise `Over` relation keeps the whole parameterized family, even
when its endpoints are related by proved rather than definitional equalities.
It is stable under reversal and concatenation, avoiding loss of boundary data.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.MappingPaths

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

def ofHomotopy {f g : C(A, B)} (H : f.Homotopy g) : Path f g where
  toContinuousMap := H.curry
  source' := H.curry_zero
  target' := H.curry_one

@[simp] theorem ofHomotopy_apply {f g : C(A, B)} (H : f.Homotopy g) (t : I) (a : A) :
    ofHomotopy H t a = H (t, a) := rfl

def toHomotopy [LocallyCompactSpace A] {f g : C(A, B)} (p : Path f g) : f.Homotopy g where
  toContinuousMap := p.toContinuousMap.uncurry
  map_zero_left a := ContinuousMap.congr_fun p.source a
  map_one_left a := ContinuousMap.congr_fun p.target a

@[simp] theorem toHomotopy_apply [LocallyCompactSpace A] {f g : C(A, B)}
    (p : Path f g) (t : I) (a : A) : toHomotopy p (t, a) = p t a := rfl

variable {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B}

/-- Equality of the entire path after applying a map, without silently identifying endpoints. -/
def Over (r : A → B) (p : Path a₀ a₁) (q : Path b₀ b₁) : Prop := ∀ t, r (p t) = q t

theorem Over.symm {r : A → B} {p : Path a₀ a₁} {q : Path b₀ b₁} (h : Over r p q) :
    Over r p.symm q.symm := fun t => h (unitInterval.symm t)

theorem Over.trans {r : A → B} {p₀ : Path a₀ a₁} {p₁ : Path a₁ a₂}
    {q₀ : Path b₀ b₁} {q₁ : Path b₁ b₂} (h₀ : Over r p₀ q₀) (h₁ : Over r p₁ q₁) :
    Over r (p₀.trans p₁) (q₀.trans q₁) := by
  intro t
  simp only [Path.trans_apply]
  split_ifs <;> first | exact h₀ _ | exact h₁ _

/-- The boundary loop produced by normalization cancels as an actual path homotopy. -/
theorem normalization_cancellation (a : Path b₀ b₁) (h : Path b₁ b₂) :
    (a.symm.trans ((Path.refl b₀).trans ((h.symm.trans a.symm).symm))).Homotopic h := by
  rw [Path.trans_symm, Path.symm_symm, Path.symm_symm]
  have hunit := Path.Homotopic.refl_trans (a.trans h)
  have hfirst := (Path.Homotopic.refl a.symm).hcomp hunit
  have hassoc := (Path.Homotopic.trans_assoc a.symm a h).symm
  have hcancel := (Path.Homotopic.symm_trans a).hcomp (Path.Homotopic.refl h)
  exact hfirst.trans (hassoc.trans (hcancel.trans (Path.Homotopic.refl_trans h)))

end Wikipedia.HopfProblem.DegreeCollapse.MappingPaths
