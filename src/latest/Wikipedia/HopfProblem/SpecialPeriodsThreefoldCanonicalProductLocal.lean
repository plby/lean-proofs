import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Products of actual local biholomorphisms with a complex line

This permits different native models for the two base manifolds.  The
product partial biholomorphism and its inverse are explicit, and use
the original product topologies and analytic atlases.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalProduct

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

local notation "I" => modelWithCornersSelf ℂ E
local notation "J" => modelWithCornersSelf ℂ F
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- An actual partial biholomorphism times the identity of the complex line. -/
def prodLine (e : PartialDiffeomorph I J M N ω) :
    PartialDiffeomorph ((I).prod I₁) ((J).prod I₁) (M × ℂ) (N × ℂ) ω where
  toFun p := (e p.1, p.2)
  invFun p := (e.symm p.1, p.2)
  source := e.source ×ˢ univ
  target := e.target ×ˢ univ
  map_source' _ h := ⟨e.map_source h.1, mem_univ _⟩
  map_target' _ h := ⟨e.map_target h.1, mem_univ _⟩
  left_inv' _ h := Prod.ext (e.left_inv h.1) rfl
  right_inv' _ h := Prod.ext (e.right_inv h.1) rfl
  open_source := e.open_source.prod isOpen_univ
  open_target := e.open_target.prod isOpen_univ
  contMDiffOn_toFun :=
    (e.contMDiffOn_toFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd
  contMDiffOn_invFun :=
    (e.contMDiffOn_invFun.comp contMDiffOn_fst (fun _ h => h.1)).prodMk contMDiffOn_snd

@[simp] theorem prodLine_apply (e : PartialDiffeomorph I J M N ω) (p : M × ℂ) :
    prodLine e p = (e p.1, p.2) := rfl

@[simp] theorem prodLine_symm_apply (e : PartialDiffeomorph I J M N ω) (p : N × ℂ) :
    (prodLine e).symm p = (e.symm p.1, p.2) := rfl

/-- Local biholomorphy of the actual base map gives local biholomorphy of
its line product, even when the native base models differ. -/
theorem isLocalDiffeomorphAt_prodLine {f : M → N} {p : M × ℂ}
    (hf : IsLocalDiffeomorphAt I J ω f p.1) :
    IsLocalDiffeomorphAt ((I).prod I₁) ((J).prod I₁) ω
      (fun q : M × ℂ => (f q.1, q.2)) p := by
  obtain ⟨e, he, hfe⟩ := hf
  refine ⟨prodLine e, ⟨he, mem_univ _⟩, ?_⟩
  intro q hq
  exact Prod.ext (hfe hq.1) rfl

theorem isLocalDiffeomorph_prodLine {f : M → N}
    (hf : IsLocalDiffeomorph I J ω f) :
    IsLocalDiffeomorph ((I).prod I₁) ((J).prod I₁) ω
      (fun q : M × ℂ => (f q.1, q.2)) :=
  fun p => isLocalDiffeomorphAt_prodLine (hf p.1)

end Wikipedia.HopfProblem.CanonicalProduct
