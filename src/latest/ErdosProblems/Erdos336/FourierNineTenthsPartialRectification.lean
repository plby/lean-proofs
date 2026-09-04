import ErdosProblems.Erdos336.RootHalfOpenInterval
import ErdosProblems.Erdos336.FrequencyQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

variable {N : ℕ} [NeZero N]

/-- A coefficient above four fifths gives a nine-tenths subset rectified in
an exact frequency quotient of sub-half span. -/
theorem fourier_nine_tenths_short_quotient_interval
    (A : Finset (ZMod N)) (k : ZMod N) (hk : k ≠ 0)
    (hF : cyclicFinsetFourier A k ≠ 0)
    (hlarge : 4 * (A.card : ℝ) <
      5 * ‖cyclicFinsetFourier A k‖) :
    ∃ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧
        m = addOrderOf k ∧
        ∃ B : Finset (ZMod N), B ⊆ A ∧
          9 * A.card < 10 * B.card ∧
          ∃ α : ZMod m, ∀ x ∈ B,
            ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m) := by
  obtain ⟨θ, hθ, B, hBA, hdense, hB⟩ :=
    exists_fourier_halfopen_slice_nine_tenths A k hF hlarge
  obtain ⟨m, hm, π, hπ, hmorder, hchar⟩ :=
    exists_frequency_quotient k hk
  let : NeZero m := ⟨hm.ne'⟩
  let r : Circle := fourierDirectionCircle A k hF
  obtain ⟨α, hα⟩ := roots_in_halfopen_semicircle m r θ hθ.1 hθ.2
  refine ⟨m, hm, π, hπ, hmorder, B, hBA, hdense, α, ?_⟩
  intro x hx
  have harc := hB x hx
  change semicircleArcMem
    (circleLowerArg (r * ZMod.toCircle (-(x * k)))) θ at harc
  rw [← hchar x] at harc
  exact hα (π x) harc

end Erdos336
