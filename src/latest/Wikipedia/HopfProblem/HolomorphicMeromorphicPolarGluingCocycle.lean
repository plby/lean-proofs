import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarGluingOverlap
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarBundleCore

/-!
# The actual scalar cocycle of local polar presentations

The transition from presentation `A` to presentation `B` is the native
holomorphic unit `q_B/q_A`, extended by zero away from the overlap. Its
identities are proved in the actual meromorphic stalk fields and then
evaluated in the original holomorphic stalks. Denominator values are not
cancelled at their pointwise zeros.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

omit [I.Boundaryless] [IsManifold I ω M] in
private theorem value_eq_one_of_germ_eq_one {U : Opens M}
    (a : HolomorphicFunctionSheaf.Section I M U) (x : U)
    (h : sectionGerm I M U x a = 1) : a x = 1 := by
  have hh : holomorphicGerm I M U x a = 1 := by
    apply ofHolomorphicGerm_injective I M x.val
    rw [map_one]
    exact h
  exact (HolomorphicFunctionSheaf.stalkEval_germ I M U x.val x.property a).symm.trans
    ((congrArg (HolomorphicFunctionSheaf.stalkEval I M x.val) hh).trans (map_one _))

omit [I.Boundaryless] [IsManifold I ω M] in
private theorem values_mul_eq_of_germs_mul_eq {U V W : Opens M}
    (a : HolomorphicFunctionSheaf.Section I M U)
    (b : HolomorphicFunctionSheaf.Section I M V)
    (c : HolomorphicFunctionSheaf.Section I M W) (x : M)
    (hxU : x ∈ U) (hxV : x ∈ V) (hxW : x ∈ W)
    (h : sectionGerm I M U ⟨x, hxU⟩ a * sectionGerm I M V ⟨x, hxV⟩ b =
      sectionGerm I M W ⟨x, hxW⟩ c) :
    a ⟨x, hxU⟩ * b ⟨x, hxV⟩ = c ⟨x, hxW⟩ := by
  have hh : holomorphicGerm I M U ⟨x, hxU⟩ a * holomorphicGerm I M V ⟨x, hxV⟩ b =
      holomorphicGerm I M W ⟨x, hxW⟩ c := by
    apply ofHolomorphicGerm_injective I M x
    rw [map_mul]
    exact h
  have ha : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M U ⟨x, hxU⟩ a) = a ⟨x, hxU⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M U x hxU a
  have hb : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M V ⟨x, hxV⟩ b) = b ⟨x, hxV⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M V x hxV b
  have hc : HolomorphicFunctionSheaf.stalkEval I M x
      (holomorphicGerm I M W ⟨x, hxW⟩ c) = c ⟨x, hxW⟩ :=
    HolomorphicFunctionSheaf.stalkEval_germ I M W x hxW c
  have hv := congrArg (HolomorphicFunctionSheaf.stalkEval I M x) hh
  rwa [map_mul, ha, hb, hc] at hv

variable {s : Section I M ⊤}

/-- The actual holomorphic overlap unit, extended by zero outside its domain. -/
def transition (A B : PolarLocal.Presentation I M s) : M → ℂ :=
  HolomorphicFunctionSheaf.extendManifoldSection I (A.overlap B) (transitionSection I M A B)

@[simp] theorem transition_apply (A B : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.overlap B) :
    transition I M A B x = transitionSection I M A B ⟨x, hx⟩ :=
  HolomorphicFunctionSheaf.extendManifoldSection_apply I (A.overlap B)
    (transitionSection I M A B) x hx

theorem transition_holomorphic (A B : PolarLocal.Presentation I M s) :
    ContMDiffOn I 𝓘(ℂ) ω (transition I M A B) ((A.domain : Set M) ∩ B.domain) := by
  intro x hx
  exact (HolomorphicFunctionSheaf.extendManifoldSection_contMDiffAt I (A.overlap B)
    (transitionSection I M A B) x hx).contMDiffWithinAt

theorem transition_ne_zero (A B : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.overlap B) : transition I M A B x ≠ 0 := by
  rw [transition_apply I M A B x hx]
  exact transitionSection_ne_zero I M A B ⟨x, hx⟩

/-- The self transition is one, including at common pointwise zeros. -/
theorem transition_self (A : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ A.domain) : transition I M A A x = 1 := by
  rw [transition_apply I M A A x ⟨hx, hx⟩]
  apply value_eq_one_of_germ_eq_one I M
  rw [transitionSection_germ_original]
  apply div_self
  exact fun h ↦ A.denominator_ne_zero ⟨x, hx⟩
    ((sectionGerm_eq_zero_iff I M A.domain ⟨x, hx⟩ A.denominator).mp h)

/-- The actual overlap units satisfy the scalar cocycle identity. -/
theorem transition_comp (A B C : PolarLocal.Presentation I M s)
    (x : M) (hx : x ∈ (A.domain : Set M) ∩ B.domain ∩ C.domain) :
    transition I M B C x * transition I M A B x = transition I M A C x := by
  have hqB : sectionGerm I M B.domain ⟨x, hx.1.2⟩ B.denominator ≠ 0 :=
    fun h ↦ B.denominator_ne_zero ⟨x, hx.1.2⟩
      ((sectionGerm_eq_zero_iff I M B.domain ⟨x, hx.1.2⟩ B.denominator).mp h)
  rw [transition_apply I M B C x ⟨hx.1.2, hx.2⟩,
    transition_apply I M A B x hx.1, transition_apply I M A C x ⟨hx.1.1, hx.2⟩]
  apply values_mul_eq_of_germs_mul_eq I M
  rw [transitionSection_germ_original, transitionSection_germ_original,
    transitionSection_germ_original]
  exact div_mul_div_cancel₀ hqB

/-- Genuine local polar presentations determine an actual scalar cocycle
on the supplied open cover. -/
def cocycle {ι : Type*} (A : ι → PolarLocal.Presentation I M s)
    (hcover : ∀ x : M, ∃ i, x ∈ (A i).domain) : PolarBundle.ScalarCocycle I M ι where
  baseSet i := (A i).domain
  isOpen_baseSet i := (A i).domain.isOpen
  cover := hcover
  transition i j := transition I M (A i) (A j)
  holomorphic_transition i j := transition_holomorphic I M (A i) (A j)
  transition_self i x hx := transition_self I M (A i) x hx
  transition_comp i j k x hx := transition_comp I M (A i) (A j) (A k) x hx

@[simp] theorem cocycle_baseSet {ι : Type*} (A : ι → PolarLocal.Presentation I M s)
    (hcover : ∀ x : M, ∃ i, x ∈ (A i).domain) (i : ι) :
    (cocycle I M A hcover).baseSet i = (A i).domain := rfl

@[simp] theorem cocycle_transition {ι : Type*} (A : ι → PolarLocal.Presentation I M s)
    (hcover : ∀ x : M, ∃ i, x ∈ (A i).domain) (i j : ι) :
    (cocycle I M A hcover).transition i j = transition I M (A i) (A j) := rfl

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarGluing
