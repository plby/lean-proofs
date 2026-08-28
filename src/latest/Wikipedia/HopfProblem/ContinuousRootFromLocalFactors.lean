import Mathlib.Analysis.Complex.BranchLogRoot

/-!
# Global continuous roots from local nonzero factors

If a function is locally a fixed global function to the `n`th power
times a continuous nonzero factor, the local factors agree on a dense
complement of the zeros and hence everywhere. On a simply connected
base, a continuous root of that global nonzero factor supplies a root
of the original function, including at its zeros.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.ContinuousRootFromLocalFactors

variable {X : Type*} [TopologicalSpace X] {f g : X → ℂ} {n : ℕ}

theorem local_factor_unique (hd : Dense {x | g x ≠ 0}) {x : X} {u v : X → ℂ}
    (hu : ContinuousAt u x) (hv : ContinuousAt v x)
    (hfu : ∀ᶠ y in 𝓝 x, f y = g y ^ n * u y)
    (hfv : ∀ᶠ y in 𝓝 x, f y = g y ^ n * v y) : u x = v x := by
  apply tendsto_nhds_unique_of_frequently_eq hu hv
  exact ((mem_closure_iff_frequently.mp (hd x)).and_eventually (hfu.and hfv)).mono
    (fun y hy => mul_left_cancel₀ (pow_ne_zero n hy.1) (hy.2.1.symm.trans hy.2.2))

theorem exists_continuous_factor (hd : Dense {x | g x ≠ 0})
    (hloc : ∀ x : X, ∃ (U : Set X) (u : X → ℂ), IsOpen U ∧ x ∈ U ∧
      ContinuousOn u U ∧ ∀ y ∈ U, u y ≠ 0 ∧ f y = g y ^ n * u y) :
    ∃ u : X → ℂ, Continuous u ∧ (∀ x, u x ≠ 0) ∧ ∀ x, f x = g x ^ n * u x := by
  choose U u hU hxU hu hfact using hloc
  let w : X → ℂ := fun x => u x x
  have hw (x : X) : ∀ y ∈ U x, w y = u x y := by
    intro y hy
    apply local_factor_unique hd ((hu y y (hxU y)).continuousAt ((hU y).mem_nhds (hxU y)))
      ((hu x y hy).continuousAt ((hU x).mem_nhds hy))
    · filter_upwards [(hU y).mem_nhds (hxU y)] with z hz
      exact (hfact y z hz).2
    · filter_upwards [(hU x).mem_nhds hy] with z hz
      exact (hfact x z hz).2
  refine ⟨w, continuous_iff_continuousAt.mpr ?_,
    (fun x => (hfact x x (hxU x)).1), (fun x => (hfact x x (hxU x)).2)⟩
  intro x
  apply ((hu x x (hxU x)).continuousAt ((hU x).mem_nhds (hxU x))).congr_of_eventuallyEq
  filter_upwards [(hU x).mem_nhds (hxU x)] with y hy
  exact hw x y hy

theorem exists_continuous_root [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (hn : n ≠ 0) (hg : Continuous g) (hd : Dense {x | g x ≠ 0})
    (hloc : ∀ x : X, ∃ (U : Set X) (u : X → ℂ), IsOpen U ∧ x ∈ U ∧
      ContinuousOn u U ∧ ∀ y ∈ U, u y ≠ 0 ∧ f y = g y ^ n * u y) :
    ∃ a : C(X, ℂ), ∀ x, a x ^ n = f x := by
  obtain ⟨u, hu, hne, hpow⟩ := exists_continuous_factor hd hloc
  have hU : IsSimplyConnected (univ : Set X) :=
    (Homeomorph.Set.univ X).toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance
  obtain ⟨v, hv, hvpow⟩ := Complex.exists_continuousOn_pow_eq hU isOpen_univ hu.continuousOn
    (by rintro ⟨x, _, hx⟩; exact hne x hx) hn
  refine ⟨⟨fun x => g x * v x, hg.mul (continuousOn_univ.mp hv)⟩, ?_⟩
  intro x
  change (g x * v x) ^ n = f x
  rw [mul_pow, hvpow, ← hpow]

end Wikipedia.HopfProblem.ContinuousRootFromLocalFactors
