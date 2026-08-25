import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real lifts of circle homeomorphisms

The quotient map from the real line to the unit additive circle is a covering
map.  We lift a circle homeomorphism and its inverse; uniqueness of covering
lifts makes the two real maps inverse homeomorphisms.  In particular the real
lift is either strictly increasing or strictly decreasing.
-/

open Set

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

/-- A continuous circle-valued map on the real line has a continuous real lift
with any prescribed value over one point. -/
theorem exists_real_lift (f : C(ℝ, AddCircle (1 : ℝ))) (a r : ℝ)
    (hr : (r : AddCircle (1 : ℝ)) = f a) :
    ∃ φ : C(ℝ, ℝ), φ a = r ∧
      ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = f t := by
  obtain ⟨φ, hφ, _⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts f a r hr
  exact ⟨φ, hφ.1, fun t => congrFun hφ.2 t⟩

/-- Every circle homeomorphism lifts to a homeomorphism of the real line.
The value over zero may be chosen arbitrarily in the correct quotient fiber. -/
theorem exists_real_homeomorph_lift
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) (r : ℝ)
    (hr : (r : AddCircle (1 : ℝ)) = e 0) :
    ∃ E : ℝ ≃ₜ ℝ, E 0 = r ∧
      ∀ t : ℝ, (E t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)) := by
  let f : C(ℝ, AddCircle (1 : ℝ)) :=
    ⟨fun t => e (t : AddCircle (1 : ℝ)),
      e.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))⟩
  obtain ⟨φ, hφzero, hφ⟩ := exists_real_lift f 0 r (by simpa [f] using hr)
  change ∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ)) at hφ
  let g : C(ℝ, AddCircle (1 : ℝ)) :=
    ⟨fun t => e.symm (t : AddCircle (1 : ℝ)),
      e.symm.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))⟩
  obtain ⟨ψ, hψr, hψ⟩ := exists_real_lift g r 0 (by simp [g, hr])
  change ∀ t : ℝ, (ψ t : AddCircle (1 : ℝ)) = e.symm (t : AddCircle (1 : ℝ)) at hψ
  have hleft : (fun t : ℝ => ψ (φ t)) = id := by
    refine (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (ψ.continuous.comp φ.continuous) continuous_id ?_ (0 : ℝ) ?_
    · ext t
      change (ψ (φ t) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
      rw [hψ, hφ]
      exact e.symm_apply_apply (t : AddCircle (1 : ℝ))
    · change ψ (φ 0) = 0
      rw [hφzero, hψr]
  have hright : (fun t : ℝ => φ (ψ t)) = id := by
    refine (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (φ.continuous.comp ψ.continuous) continuous_id ?_ r ?_
    · ext t
      change (φ (ψ t) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ))
      rw [hφ, hψ]
      exact e.apply_symm_apply (t : AddCircle (1 : ℝ))
    · change φ (ψ r) = r
      rw [hψr, hφzero]
  let E : ℝ ≃ₜ ℝ :=
    { toFun := φ
      invFun := ψ
      left_inv := fun t => congrFun hleft t
      right_inv := fun t => congrFun hright t
      continuous_toFun := φ.continuous
      continuous_invFun := ψ.continuous }
  exact ⟨E, hφzero, hφ⟩

/-- A homeomorphic real lift is increasing or decreasing, with no extra
orientation hypothesis on the circle homeomorphism. -/
theorem exists_strictMono_or_strictAnti_lift
    (e : AddCircle (1 : ℝ) ≃ₜ AddCircle (1 : ℝ)) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧
      (∀ t : ℝ, (φ t : AddCircle (1 : ℝ)) = e (t : AddCircle (1 : ℝ))) ∧
      (StrictMono φ ∨ StrictAnti φ) := by
  let r : ℝ := AddCircle.equivIco (1 : ℝ) 0 (e 0)
  have hr : (r : AddCircle (1 : ℝ)) = e 0 := AddCircle.coe_equivIco
  obtain ⟨E, _, hE⟩ := exists_real_homeomorph_lift e r hr
  exact ⟨E, E.continuous, hE, E.continuous.strictMono_of_inj E.injective⟩

end

end Puzzling139335.CentralRotation.BoundaryOrientation
