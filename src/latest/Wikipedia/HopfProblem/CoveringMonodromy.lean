import Mathlib.Topology.Homotopy.Lifting

/-!
# Monodromy of a commutative square of coverings

This elementary naturality statement compares the actual endpoint of a lifted
path in two covers. It will identify the map on fundamental groups induced by
the inclusion of a cusp fibre.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem

/-- A continuous map of covering spaces carries lifted endpoints to lifted
endpoints. No simple-connectivity assumption is needed. -/
theorem covering_monodromy_naturality
    {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y]
    {p : E → X} {q : F → Y} (hp : IsCoveringMap p) (hq : IsCoveringMap q)
    (r : ContinuousMap E F) (f : ContinuousMap X Y)
    (hcomm : ∀ z, q (r z) = f (p z)) (e : E)
    (γ : Path.Homotopic.Quotient (p e) (p e)) :
    (hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ : F) =
      r (hp.monodromy γ ⟨e, rfl⟩ : E) := by
  let e' : p ⁻¹' {p e} := hp.monodromy γ ⟨e, rfl⟩
  let f' : q ⁻¹' {f (p e)} :=
    ⟨r e', (hcomm e').trans (congrArg f e'.property)⟩
  have hc : (ContinuousMap.mk q hq.continuous).comp r =
      f.comp ⟨p, hp.continuous⟩ := ContinuousMap.ext hcomm
  have he : hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ = f' := by
    apply hq.monodromy_eq_of_map_eq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map r)
    apply eq_of_heq
    have hmap {f₁ f₂ : ContinuousMap E Y} (h : f₁ = f₂) :
        HEq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₁)
          ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₂) := by
      subst f₂
      rfl
    apply (heq_of_eq Path.Homotopic.Quotient.map_comp.symm).trans
    apply (hmap hc).trans
    rw [Path.Homotopic.Quotient.map_comp, hp.map_liftPathQuotient]
    have hm : (γ.cast rfl (show p e' = p e from e'.property)).map f =
        (γ.map f).cast rfl (congrArg f e'.property) :=
      Path.Homotopic.Quotient.map_cast γ
    apply (heq_of_eq hm).trans
    exact Path.Homotopic.Quotient.cast_heq _ _ |>.trans
      (Path.Homotopic.Quotient.cast_heq _ _).symm
  exact congrArg Subtype.val he

end Wikipedia.HopfProblem
