import Wikipedia.NoExoticSixSphere.JamesWordTopology
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Homotopy.Basic

/-!
# Based generator homotopies extend to the original full James space

Curry the actual homotopy into continuous paths in the target monoid.
Its value at the basepoint is the exact constant identity path. The
original pointed free-monoid lift is continuous for the original final
word topology, and evaluation gives a homotopy fixing the empty word.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.JamesHomotopyLift

open NoExoticSixSphere

variable {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
variable [Monoid M] [ContinuousMul M]
variable {x₀ : X} {f g : C(X, M)}
variable (H : f.HomotopyRel g {x₀})

def path (x : X) : C(I, M) :=
  H.toContinuousMap.comp ⟨fun t ↦ (t, x), continuous_id.prodMk continuous_const⟩

omit [Monoid M] [ContinuousMul M] in
theorem path_continuous : Continuous (path H) :=
  ContinuousMap.continuous_of_continuous_uncurry (path H)
    (H.continuous.comp continuous_swap)

omit [ContinuousMul M] in
theorem path_basepoint (hf : f x₀ = 1) : path H x₀ = 1 := by
  apply ContinuousMap.ext
  intro t
  exact (H.eq_fst t (Set.mem_singleton x₀)).trans hf

def family (hf : f x₀ = 1) : C(James.Space X x₀, C(I, M)) :=
  ⟨James.lift x₀ (path H),
    James.continuous_lift x₀ (path H) (path_basepoint H hf) (path_continuous H)⟩

def evaluationHom (t : I) : C(I, M) →* M where
  toFun p := p t
  map_one' := rfl
  map_mul' _ _ := rfl

theorem family_zero (hf : f x₀ = 1) (w : James.Space X x₀) :
    family H hf w 0 = James.lift x₀ f w := by
  have he : (evaluationHom (M := M) 0).comp (James.lift x₀ (path H)) =
      James.lift x₀ f := by
    apply James.hom_ext x₀
    intro x
    change James.lift x₀ (path H) (James.letter x₀ x) 0 =
      James.lift x₀ f (James.letter x₀ x)
    rw [James.lift_letter x₀ (path H) (path_basepoint H hf), James.lift_letter x₀ f hf]
    exact H.apply_zero x
  exact DFunLike.congr_fun he w

theorem family_one (hf : f x₀ = 1) (hg : g x₀ = 1) (w : James.Space X x₀) :
    family H hf w 1 = James.lift x₀ g w := by
  have he : (evaluationHom (M := M) 1).comp (James.lift x₀ (path H)) =
      James.lift x₀ g := by
    apply James.hom_ext x₀
    intro x
    change James.lift x₀ (path H) (James.letter x₀ x) 1 =
      James.lift x₀ g (James.letter x₀ x)
    rw [James.lift_letter x₀ (path H) (path_basepoint H hf), James.lift_letter x₀ g hg]
    exact H.apply_one x
  exact DFunLike.congr_fun he w

def lifted (hf : f x₀ = 1) (hg : g x₀ = 1) :
    (⟨James.lift x₀ f, James.continuous_lift x₀ f hf f.continuous⟩ :
      C(James.Space X x₀, M)).HomotopyRel
      ⟨James.lift x₀ g, James.continuous_lift x₀ g hg g.continuous⟩ {1} where
  toFun u := family H hf u.2 u.1
  continuous_toFun := continuous_eval.comp
    (((family H hf).continuous.comp continuous_snd).prodMk continuous_fst)
  map_zero_left w := family_zero H hf w
  map_one_left w := family_one H hf hg w
  prop' t w hw := by
    have he : w = 1 := hw
    subst w
    change James.lift x₀ (path H) 1 t = James.lift x₀ f 1
    rw [map_one, map_one]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.JamesHomotopyLift
