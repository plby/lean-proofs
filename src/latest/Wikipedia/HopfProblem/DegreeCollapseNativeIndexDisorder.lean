import Wikipedia.HopfProblem.DegreeCollapseFiniteIndexDisorder
import Wikipedia.HopfProblem.DegreeCollapseNativeIndexExchange

/-!
# Intrinsic finite disorder for the actual native Morse function

The natural-valued disorder is defined from the actual critical set,
critical values and chart-independent native indices. Transport through
equality of critical sets retains its value. The constructed exchange of
an adjacent strict index inversion decreases it strictly.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse
open Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ}

open Classical in
def nativeIndexDisorder (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) : ℕ :=
  if hfinite : (criticalPoints E f).Finite then
    let _ := hfinite.fintype
    finiteIndexDisorder (fun x : criticalPoints E f => f x)
      (fun x : criticalPoints E f => nativeMorseIndex E f x)
  else 0

theorem nativeIndexDisorder_eq_of_finite (hfinite : (criticalPoints E f).Finite) :
    letI := hfinite.fintype
    nativeIndexDisorder E f = finiteIndexDisorder (fun x : criticalPoints E f => f x)
      (fun x : criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  simp only [nativeIndexDisorder, dif_pos hfinite]

theorem nativeIndexDisorder_transport (hfinite : (criticalPoints E f).Finite)
    (hcrit : criticalPoints E g = criticalPoints E f)
    (hindex : ∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) :
    letI := hfinite.fintype
    nativeIndexDisorder E g = finiteIndexDisorder (fun x : criticalPoints E f => g x)
      (fun x : criticalPoints E f => nativeMorseIndex E f x) := by
  classical
  let _ := hfinite.fintype
  have hgfinite : (criticalPoints E g).Finite := hcrit.symm ▸ hfinite
  let _ := hgfinite.fintype
  let e : criticalPoints E f ≃ criticalPoints E g := Equiv.setCongr hcrit.symm
  rw [nativeIndexDisorder_eq_of_finite hgfinite]
  rw [← finiteIndexDisorder_comp_equiv (fun x : criticalPoints E g => g x)
    (fun x : criticalPoints E g => nativeMorseIndex E g x) e]
  have hw : ((fun x : criticalPoints E g => nativeMorseIndex E g x) ∘ e) =
      fun x : criticalPoints E f => nativeMorseIndex E f x := by
    funext x
    exact hindex x x.property
  rw [hw]
  rfl

theorem nativeIndexDisorder_exchange_lt (hfinite : (criticalPoints E f).Finite)
    (hinj : InjOn f (criticalPoints E f)) (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindexlt : nativeMorseIndex E f q < nativeMorseIndex E f p)
    (hcrit : criticalPoints E g = criticalPoints E f) (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ criticalPoints E f, x ≠ p.val → x ≠ q.val → g =ᶠ[𝓝 x] f)
    (hindex : ∀ x ∈ criticalPoints E f, nativeMorseIndex E g x = nativeMorseIndex E f x) :
    nativeIndexDisorder E g < nativeIndexDisorder E f := by
  classical
  let _ : DecidableEq (criticalPoints E f) := fun a b => Classical.propDecidable (a = b)
  let _ := hfinite.fintype
  have hform : (fun x : criticalPoints E f => g x) =
      (fun x : criticalPoints E f => f x) ∘ Equiv.swap p q := by
    funext x
    by_cases hxp : x = p
    · subst x
      simpa only [comp_apply, Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [comp_apply, Equiv.swap_apply_right] using hgq
    have hh := (hothers x x.property (fun h => hxp (Subtype.ext h))
      (fun h => hxq (Subtype.ext h))).self_of_nhds
    simpa only [comp_apply, Equiv.swap_apply_def, if_neg hxp, if_neg hxq] using hh
  rw [nativeIndexDisorder_transport hfinite hcrit hindex,
    nativeIndexDisorder_eq_of_finite hfinite, hform]
  have hi : Injective (fun x : criticalPoints E f => f x) :=
    fun x y h => Subtype.ext (hinj x.property y.property h)
  exact finiteIndexDisorder_swap_lt (h := fun x : criticalPoints E f => f x) hi
    (fun x : criticalPoints E f => nativeMorseIndex E f x) (p := p) (q := q)
    hpq hconsecutive hindexlt

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
