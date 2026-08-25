import Util.Bernays.FormCounting

/-!
# Bernays' theorem with one positive constant for every form of a discriminant

The constant combines the uniform coprime-class asymptotic with the convergent
sum over discriminant-prime parts. The counting function and normalization are
those of the original statement, including the represented value zero.
-/

open Filter Topology Asymptotics

namespace BinQuadForm

theorem B_isEquivalent {f : BinQuadForm} (hf : f.PosDef) (hp : f.Primitive) :
    (fun x : ℝ => (f.B x : ℝ)) ~[atTop]
      (fun x : ℝ => Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2) *
        x / Real.sqrt (Real.log x)) := by
  let C := Bernays.fullClassConstant (f.canonical_order_discr.trans_lt hf.2)
  have hC : C ≠ 0 := (Bernays.fullClassConstant_pos _).ne'
  apply (Bernays.real_asymptotic_iff_nat f C).mpr
  apply isEquivalent_of_tendsto_one
  have h := (B_nat_limit hf hp).div_const C
  rw [div_self hC] at h
  apply h.congr'
  filter_upwards [] with N
  change ((f.B (N : ℝ) : ℝ) / Bernays.scale N) / C = _
  rw [div_div, mul_comm (Bernays.scale N) C]
  simp only [Bernays.scale, mul_div_assoc, Pi.div_apply]

end BinQuadForm

namespace Bernays

noncomputable def discriminantBernaysConstant (Δ : ℤ) : ℝ :=
  if h : (discriminantTrace Δ) ^ 2 + 4 * discriminantConstant Δ < 0 then fullClassConstant h else 1

theorem discriminantBernaysConstant_pos (Δ : ℤ) : 0 < discriminantBernaysConstant Δ := by
  unfold discriminantBernaysConstant
  split_ifs with h
  · exact fullClassConstant_pos h
  · norm_num

theorem bernays_theorem
    (Δ : ℤ) (_hΔnonsq : ¬ ∃ z : ℤ, z * z = Δ) :
    ∃ CΔ : ℝ, 0 < CΔ ∧
      ∀ f : BinQuadForm,
        f.Primitive →
        f.PosDef →
        f.discr = Δ →
        (fun x : ℝ => (f.B x : ℝ))
          ~[Filter.atTop]
          (fun x : ℝ => CΔ * x / Real.sqrt (Real.log x)) := by
  refine ⟨discriminantBernaysConstant Δ, discriminantBernaysConstant_pos Δ, ?_⟩
  intro f hp hf hdiscr
  rw [← hdiscr]
  have hD := f.canonical_order_discr.trans_lt hf.2
  rw [discriminantBernaysConstant, dif_pos hD]
  exact BinQuadForm.B_isEquivalent hf hp

end Bernays
