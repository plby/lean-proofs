-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DeltaRho

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cardinal-arithmetic facts about `δ(ρ) = deltaRho ρ`

For an infinite cardinal `ρ`, `δ(ρ) = min{δ : ρ^δ > ρ}`.  This file proves the
basic facts about `δ(ρ)` used in the Erdős–Galvin–Hajnal construction (E3):

* `deltaRho_pow_le`  : `θ < δ(ρ) → ρ^θ ≤ ρ`;
* `aleph0_le_deltaRho` : `ℵ₀ ≤ δ(ρ)`;
* `deltaRho_le_cof`  : `δ(ρ) ≤ (ρ.ord).cof` (König);
* `deltaRho_le`      : `δ(ρ) ≤ ρ`;
* `deltaRho_regular` : `(δ(ρ).ord).cof = δ(ρ)` (regularity).
-/

open Cardinal Ordinal

namespace Erdos1177

variable {ρ : Cardinal.{u}}

/-- `ρ < ρ ^ (deltaRho ρ)`: the defining set has `deltaRho ρ` as a member. -/
theorem lt_pow_deltaRho (hρ : ℵ₀ ≤ ρ) : ρ < ρ ^ (deltaRho ρ) := by
  have hne : ({δ | ρ < ρ ^ δ} : Set Cardinal).Nonempty := ⟨ρ, deltaRho_mem hρ⟩
  have hmem := csInf_mem hne
  simpa [deltaRho] using! hmem

/-- For `θ < δ(ρ)`, we have `ρ^θ ≤ ρ`. -/
theorem deltaRho_pow_le {θ : Cardinal} (hθ : θ < deltaRho ρ) :
    ρ ^ θ ≤ ρ := by
  by_contra h
  push_neg at h
  have : deltaRho ρ ≤ θ := csInf_le (OrderBot.bddBelow _) h
  exact absurd hθ (not_lt.mpr this)

/-- `ℵ₀ ≤ δ(ρ)`: for finite `θ`, `ρ^θ = ρ`, so no finite `θ` lies in the
defining set. -/
theorem aleph0_le_deltaRho (hρ : ℵ₀ ≤ ρ) : ℵ₀ ≤ deltaRho ρ := by
  rw [deltaRho]
  refine le_csInf ⟨ρ, deltaRho_mem hρ⟩ ?_
  intro d hd
  by_contra h
  push_neg at h
  exact absurd (Cardinal.pow_le hρ h) (not_le.mpr hd)

/-- König: `δ(ρ) ≤ (ρ.ord).cof`. -/
theorem deltaRho_le_cof (hρ : ℵ₀ ≤ ρ) : deltaRho ρ ≤ (ρ.ord).cof := by
  have : (ρ.ord).cof ∈ {δ | ρ < ρ ^ δ} := Cardinal.lt_power_cof hρ
  exact csInf_le (OrderBot.bddBelow _) this

/-- `δ(ρ) ≤ ρ`. -/
theorem deltaRho_le (hρ : ℵ₀ ≤ ρ) : deltaRho ρ ≤ ρ :=
  le_trans (deltaRho_le_cof hρ) (Ordinal.cof_ord_le ρ)

/-- `δ(ρ)` is regular: `(δ(ρ).ord).cof = δ(ρ)`. -/
theorem deltaRho_regular (hρ : ℵ₀ ≤ ρ) : (deltaRho ρ).ord.cof = deltaRho ρ := by
  set δ := deltaRho ρ with hδdef
  have hwo : IsWellOrder δ.ord.ToType (· < ·) := inferInstance
  refine le_antisymm (Ordinal.cof_ord_le δ) ?_
  by_contra hcon
  push_neg at hcon
  have hδinf : ℵ₀ ≤ δ := aleph0_le_deltaRho hρ
  have hIioLt : ∀ s : δ.ord.ToType, #(Set.Iio s) < δ := by
    intro s
    exact Cardinal.mk_Iio_toType_ord_lt s
  have hIicLt : ∀ s : δ.ord.ToType, #(Set.Iic s) < δ := by
    intro s
    have hu : (Set.Iic s : Set δ.ord.ToType) = (Set.Iio s ∪ {s} : Set δ.ord.ToType) := by
      ext x; simp [le_iff_lt_or_eq]
    rw [hu]
    calc #((Set.Iio s ∪ {s} : Set δ.ord.ToType)) ≤ #(Set.Iio s) + #({s} : Set δ.ord.ToType) :=
            Cardinal.mk_union_le _ _
      _ = #(Set.Iio s) + 1 := by rw [Cardinal.mk_singleton]
      _ < δ := Cardinal.add_lt_of_lt hδinf (hIioLt s) (lt_of_lt_of_le one_lt_aleph0 hδinf)
  obtain ⟨S, hSub, hScard⟩ := Order.exists_cof_eq δ.ord.ToType
  rw [Ordinal.cof_toType] at hScard
  have hScardδ : #S < δ := by rw [hScard]; exact hcon
  have hcover : (⋃ (s : S), Set.Iic (s : δ.ord.ToType)) = (Set.univ : Set δ.ord.ToType) := by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    obtain ⟨s, hs, hxs⟩ := hSub x
    exact ⟨⟨s, hs⟩, hxs⟩
  have hδcard : #(δ.ord.ToType) = δ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
  have hle : δ ≤ Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType))) := by
    calc δ = #(δ.ord.ToType) := hδcard.symm
      _ = #(⋃ (s : S), Set.Iic (s : δ.ord.ToType)) := by rw [hcover, Cardinal.mk_univ]
      _ ≤ Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType))) := Cardinal.mk_iUnion_le_sum_mk
  have hpow : ρ ^ δ ≤ ρ := by
    calc ρ ^ δ ≤ ρ ^ (Cardinal.sum (fun s : S => #(Set.Iic (s : δ.ord.ToType)))) :=
          Cardinal.power_le_power_left ((lt_of_lt_of_le Cardinal.aleph0_pos hρ).ne') hle
      _ = Cardinal.prod (fun s : S => ρ ^ #(Set.Iic (s : δ.ord.ToType))) := Cardinal.power_sum ..
      _ ≤ Cardinal.prod (fun _ : S => ρ) :=
          Cardinal.prod_le_prod _ _ (fun s => deltaRho_pow_le (hIicLt s))
      _ = ρ ^ #S := by rw [Cardinal.prod_const, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ ρ := deltaRho_pow_le hScardδ
  exact absurd (lt_pow_deltaRho hρ) (not_lt.mpr hpow)

/-- `δ(ρ)` is an infinite regular cardinal (as an `IsRegular` fact). -/
theorem deltaRho_isRegular (hρ : ℵ₀ ≤ ρ) : (deltaRho ρ).IsRegular :=
  ⟨aleph0_le_deltaRho hρ, (deltaRho_regular hρ).symm.le⟩

end Erdos1177
