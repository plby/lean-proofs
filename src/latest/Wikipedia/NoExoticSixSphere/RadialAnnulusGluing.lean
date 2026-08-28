import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates
import Mathlib.Topology.Order.ProjIcc

/-!
# Gluing two prescribed annulus collars to an actual cylinder

Rescale the cylinder parameter between the two chosen radii and leave
both collars unchanged. Exact endpoint agreement proves continuity at
the seams. A specified open region is retained at every interior point;
the construction itself does not require smoothness at either seam.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.RadialAnnulusGluing

open GLOrthonormalization SphereAnnulus

theorem exists_map {p : ℕ} {X : Type*} [TopologicalSpace X]
    (b : Sphere p) (ρ₀ ρ₁ : ℝ) (hρ : ρ₀ < ρ₁)
    (g₀ g₁ : Vector (p + 1) → X)
    (hg₀ : ContinuousOn g₀ {x | x ∈ domain p ∧ ‖x‖ ≤ ρ₀})
    (hg₁ : ContinuousOn g₁ {x | x ∈ domain p ∧ ρ₁ ≤ ‖x‖})
    (H : C(unitInterval × Sphere p, X))
    (hH₀ : ∀ s, H (0, s) = g₀ (ρ₀ • s.val))
    (hH₁ : ∀ s, H (1, s) = g₁ (ρ₁ • s.val))
    (V : Set X) (hHV : ∀ z, H z ∈ V)
    (hg₀V : ∀ x ∈ domain p, 1 < ‖x‖ → ‖x‖ ≤ ρ₀ → g₀ x ∈ V)
    (hg₁V : ∀ x ∈ domain p, ‖x‖ < 2 → ρ₁ ≤ ‖x‖ → g₁ x ∈ V) :
    ∃ G : C(domain p, X),
      (∀ x : domain p, ‖x.val‖ ≤ ρ₀ → G x = g₀ x.val) ∧
      (∀ x : domain p, ρ₁ ≤ ‖x.val‖ → G x = g₁ x.val) ∧
      ∀ x : domain p, 1 < ‖x.val‖ → ‖x.val‖ < 2 → G x ∈ V := by
  let q : C(domain p, Sphere p) := ContinuousMap.snd.comp (toCylinder b)
  have hq (x : domain p) : ‖x.val‖ • (q x).val = x.val := by
    change ‖x.val‖ • (SphereRadialRetraction.retract b x.val).val = x.val
    rw [SphereRadialRetraction.retract, dif_neg (ne_zero x)]
    exact NormedSpace.norm_smul_normalize x.val
  let u : C(domain p, unitInterval) :=
    ⟨fun x ↦ projIcc 0 1 zero_le_one ((‖x.val‖ - ρ₀) / (ρ₁ - ρ₀)),
      continuous_projIcc.comp
        (((continuous_norm.comp continuous_subtype_val).sub continuous_const).div_const _)⟩
  let J : C(domain p, X) := H.comp (u.prodMk q)
  have hJ₀ (x : domain p) (hx : ‖x.val‖ = ρ₀) : J x = g₀ x.val := by
    change H (projIcc 0 1 zero_le_one ((‖x.val‖ - ρ₀) / (ρ₁ - ρ₀)), q x) = _
    rw [hx, sub_self, zero_div]
    have hp : projIcc 0 1 zero_le_one (0 : ℝ) = (0 : unitInterval) :=
      projIcc_of_mem zero_le_one ⟨le_rfl, zero_le_one⟩
    rw [hp, hH₀, ← hx, hq]
  have hJ₁ (x : domain p) (hx : ‖x.val‖ = ρ₁) : J x = g₁ x.val := by
    change H (projIcc 0 1 zero_le_one ((‖x.val‖ - ρ₀) / (ρ₁ - ρ₀)), q x) = _
    rw [hx, div_self (sub_pos.mpr hρ).ne']
    have hp : projIcc 0 1 zero_le_one (1 : ℝ) = (1 : unitInterval) :=
      projIcc_of_mem zero_le_one ⟨zero_le_one, le_rfl⟩
    rw [hp, hH₁, ← hx, hq]
  let F : C(domain p, X) := {
    toFun := fun x ↦ if ‖x.val‖ ≤ ρ₁ then J x else g₁ x.val
    continuous_toFun := by
      apply continuous_if_le (continuous_norm.comp continuous_subtype_val) continuous_const
      · exact J.continuous.continuousOn
      · exact hg₁.comp continuous_subtype_val.continuousOn
          (fun x hx ↦ ⟨x.property, hx⟩)
      · exact hJ₁ }
  let G : C(domain p, X) := {
    toFun := fun x ↦ if ‖x.val‖ ≤ ρ₀ then g₀ x.val else F x
    continuous_toFun := by
      apply continuous_if_le (continuous_norm.comp continuous_subtype_val) continuous_const
      · exact hg₀.comp continuous_subtype_val.continuousOn
          (fun x hx ↦ ⟨x.property, hx⟩)
      · exact F.continuous.continuousOn
      · intro x hx
        change ‖x.val‖ = ρ₀ at hx
        change g₀ x.val = if ‖x.val‖ ≤ ρ₁ then J x else g₁ x.val
        rw [if_pos (hx.trans_le hρ.le)]
        exact (hJ₀ x hx).symm }
  refine ⟨G, ?_, ?_, ?_⟩
  · intro x hx
    exact if_pos hx
  · intro x hx
    change (if ‖x.val‖ ≤ ρ₀ then g₀ x.val else
      if ‖x.val‖ ≤ ρ₁ then J x else g₁ x.val) = g₁ x.val
    rw [if_neg (not_le.mpr (hρ.trans_le hx))]
    by_cases hle : ‖x.val‖ ≤ ρ₁
    · rw [if_pos hle]
      exact hJ₁ x (le_antisymm hle hx)
    · exact if_neg hle
  · intro x hx₀ hx₁
    change (if ‖x.val‖ ≤ ρ₀ then g₀ x.val else
      if ‖x.val‖ ≤ ρ₁ then J x else g₁ x.val) ∈ V
    by_cases hle₀ : ‖x.val‖ ≤ ρ₀
    · rw [if_pos hle₀]
      exact hg₀V x.val x.property hx₀ hle₀
    · rw [if_neg hle₀]
      by_cases hle₁ : ‖x.val‖ ≤ ρ₁
      · rw [if_pos hle₁]
        exact hHV _
      · rw [if_neg hle₁]
        exact hg₁V x.val x.property hx₁ (le_of_not_ge hle₁)

end NoExoticSixSphere.RadialAnnulusGluing
