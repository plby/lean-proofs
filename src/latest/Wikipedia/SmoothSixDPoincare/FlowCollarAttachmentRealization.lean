import Wikipedia.SmoothSixDPoincare.FlowCollarBoundary

/-!
# The retained collar's whole-sublevel attachment realization

The inverse collar homeomorphism is the chosen attachment realization.
Its frontier, fixed-point, and backward-orbit formulas are retained exactly,
so the same realization can be inserted into the native surgery record.
-/

noncomputable section

open Set

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData

variable {M : Type*} [TopologicalSpace M] [T2Space M] {f : M → ℝ} {b : ℝ}
  {F : Flow ℝ M} {A : Set M} [CompactSpace ↥({x : M | f x ≤ b})]
  (d : FlowCollarData F A {x | f x ≤ b})

def sublevelRealization : A ≃ₜ {x : M // f x ≤ b} := d.homeomorph.symm

theorem sublevelRealization_frontier
    (hb : frontier {x | f x ≤ b} = {x | f x = b}) (x : A) :
    f (d.sublevelRealization x).val = b ↔ x.val ∈ frontier A := by
  have h := d.homeomorph_mem_frontier_iff (d.homeomorph.symm x)
  rw [d.homeomorph.apply_symm_apply, hb] at h
  exact h.symm

theorem sublevelRealization_fixed
    (hb : frontier {x | f x ≤ b} = {x | f x = b}) (x : A) (hx : f x.val = b) :
    (d.sublevelRealization x).val = x.val := by
  let y : ↥({x : M | f x ≤ b}) := ⟨x.val, hx.le⟩
  have hy : y.val ∈ frontier {z : M | f z ≤ b} := by rw [hb]; exact hx
  have heq : d.homeomorph y = x :=
    Subtype.ext (d.homeomorph_fixed_on_common_frontier y x.property hy)
  have hh := congrArg d.homeomorph.symm heq
  rw [d.homeomorph.symm_apply_apply] at hh
  exact congrArg (fun z : ↥({x : M | f x ≤ b}) => z.val) hh.symm

theorem sublevelRealization_orbit
    (hb : frontier {x | f x ≤ b} = {x | f x = b}) (x : A) (hx : x.val ∈ frontier A)
    (t : ℝ) (ht : t ≤ 0) (hlevel : f (F t x.val) = b) :
    (d.sublevelRealization x).val = F t x.val := by
  apply d.homeomorph_symm_eq_flow_of_mem_frontier x hx ht
  rw [hb]
  exact hlevel

end Wikipedia.SmoothSixDPoincare.FlowConstruction.FlowCollarData
