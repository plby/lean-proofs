import Wikipedia.NoExoticSixSphere.FlatDoublePointClosureChart

/-!
# Swapping actual double points negates the local curve coordinate

Swapping preserves the actual closed double-point set. Recovery converts it
to reflection in signed half-separation. The reflection-invariant zero chart
therefore gives a swap-invariant local source and negates the actual coordinate.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U] [NormedAddCommGroup U] in
theorem recover_swap (r : (U × ℝ) × (U × ℝ)) (hr : r.1.1 = r.2.1) :
    recover r.swap = ImplicitCurve.reflectPoint (recover r) := by
  rcases r with ⟨⟨u, z⟩, ⟨v, w⟩⟩
  change u = v at hr
  subst v
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · dsimp [recover, ImplicitCurve.reflectPoint]
      ring
  · dsimp [recover, ImplicitCurve.reflectPoint]
    ring

omit [FiniteDimensional ℝ U] [NormedSpace ℝ U]
  [CompleteSpace F] [NormedSpace ℝ F] [NormedAddCommGroup F] in
theorem swap_mem_closure (h : U × ℝ → F) {r : (U × ℝ) × (U × ℝ)}
    (hr : r ∈ closure (doublePoints h)) : r.swap ∈ closure (doublePoints h) := by
  have hm : MapsTo Prod.swap (doublePoints h) (doublePoints h) :=
    fun q hq ↦ ⟨hq.1.symm, hq.2.symm⟩
  exact hm.closure continuous_swap hr

def swapClosure (h : U × ℝ → F) : closure (doublePoints h) ≃ₜ closure (doublePoints h) where
  toFun r := ⟨r.val.swap, swap_mem_closure h r.property⟩
  invFun r := ⟨r.val.swap, swap_mem_closure h r.property⟩
  left_inv r := Subtype.ext (Prod.swap_swap r.val)
  right_inv r := Subtype.ext (Prod.swap_swap r.val)
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

theorem closedRecover_swap (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (r : closure (doublePoints h)) :
    closedRecover h hh (swapClosure h r) =
      ImplicitCurve.reflection (dividedDifference h)
        (fun p s ↦ dividedDifference_even h p.1 p.2 s) (closedRecover h hh r) :=
  Subtype.ext (recover_swap r.val (closure_head_eq h r.property))

variable (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
  (d : OpenPartialHomeomorph {q : (U × ℝ) × ℝ // dividedDifference h q = 0} ℝ)
  (hd : ∀ q, d q = q.val.2) (r₀ : closure (doublePoints h))

theorem closureChart_source_swap
    (hreflect : ∀ q ∈ d.source, ImplicitCurve.reflection (dividedDifference h)
      (fun p s ↦ dividedDifference_even h p.1 p.2 s) q ∈ d.source)
    {r : closure (doublePoints h)} (hr : r ∈ (closureChart h hh d hd r₀).source) :
    swapClosure h r ∈ (closureChart h hh d hd r₀).source := by
  change closedRecover h hh (swapClosure h r) ∈ d.source
  rw [closedRecover_swap]
  exact hreflect _ hr

theorem closureChart_swap (r : closure (doublePoints h)) :
    closureChart h hh d hd r₀ (swapClosure h r) = -closureChart h hh d hd r₀ r := by
  rw [closureChart_apply, closureChart_apply]
  change (r.val.2.2 - r.val.1.2) / 2 = -((r.val.1.2 - r.val.2.2) / 2)
  ring

end NoExoticSixSphere.FlatDoubleCurve
