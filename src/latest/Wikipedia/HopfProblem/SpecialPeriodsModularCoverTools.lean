import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Injectivity tools for the regular modular covering

Path lifting transports a singleton fibre to every fibre of a covering
over a path-connected base. An open map from a Hausdorff space is injective
as soon as it is injective over a dense subset of its target. These facts
are independent of the modular function. The complements of countable
subsets of the complex plane supply the path-connected regular targets.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularCoverTools

/-- A covering of a path-connected base with at most one point in a single
fibre is injective everywhere. No finiteness assumption on the fibres is needed. -/
theorem injective_of_covering_singleton_fibre
    {X B : Type*} [TopologicalSpace X] [TopologicalSpace B] [PathConnectedSpace B]
    {f : X → B} (hf : IsCoveringMap f) (b₀ : B) (h₀ : Subsingleton (f ⁻¹' {b₀})) :
    Function.Injective f := by
  intro x y hxy
  let γ : Path.Homotopic.Quotient (f x) b₀ :=
    .mk (PathConnectedSpace.somePath (f x) b₀)
  have he : (⟨x, rfl⟩ : f ⁻¹' {f x}) = ⟨y, hxy.symm⟩ :=
    (hf.monodromy_bijective γ).1 (h₀.elim _ _)
  exact congrArg Subtype.val he

/-- Two distinct points of a Hausdorff source have disjoint open
neighbourhoods. Openness and density then detect their failure of injectivity. -/
theorem injective_of_open_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    {f : X → Y} {D : Set Y} (hf : IsOpenMap f) (hD : Dense D)
    (hi : Set.InjOn f (f ⁻¹' D)) : Function.Injective f := by
  intro x y hxy
  by_contra hne
  obtain ⟨U, V, hU, hV, hx, hy, hUV⟩ := t2_separation hne
  have hnonempty : (f '' U ∩ f '' V).Nonempty :=
    ⟨f x, ⟨x, hx, rfl⟩, y, hy, hxy.symm⟩
  obtain ⟨z, hzD, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ :=
    hD.exists_mem_open ((hf U hU).inter (hf V hV)) hnonempty
  have huv : u = v := hi (by simpa only [mem_preimage, huz] using hzD)
    (by simpa only [mem_preimage, hvz] using hzD) (huz.trans hvz.symm)
  subst v
  exact hUV.le_bot ⟨hu, hv⟩

theorem complex_compl_countable_pathConnected {S : Set ℂ} (hS : S.Countable) :
    PathConnectedSpace ↥(Sᶜ) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (hS.isPathConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex]))

theorem complex_compl_pair_pathConnected (a b : ℂ) :
    PathConnectedSpace ↥(({a, b} : Set ℂ)ᶜ) :=
  complex_compl_countable_pathConnected (Set.toFinite _).countable

theorem complex_compl_countable_dense {S : Set ℂ} (hS : S.Countable) : Dense Sᶜ :=
  hS.dense_compl ℝ

theorem complex_compl_pair_dense (a b : ℂ) : Dense (({a, b} : Set ℂ)ᶜ) :=
  complex_compl_countable_dense (Set.toFinite _).countable

end Wikipedia.HopfProblem.SpecialPeriods.ModularCoverTools
