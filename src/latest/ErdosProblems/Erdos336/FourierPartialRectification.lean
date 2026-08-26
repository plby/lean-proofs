import ErdosProblems.Erdos336.FrequencyQuotient

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

variable {N : ℕ} [NeZero N]

/-- A nonzero Fourier direction produces a surjective quotient of size equal
to the frequency order, and the positive half-plane slice lies in a cyclic
interval of span strictly less than half that quotient. -/
theorem positiveHalf_short_quotient_interval
    (A : Finset (ZMod N)) (k : ZMod N) (hk : k ≠ 0)
    (hF : cyclicFinsetFourier A k ≠ 0) :
    ∃ (m : ℕ) (hm : 0 < m),
      let _ : NeZero m := ⟨hm.ne'⟩
      ∃ (π : ZMod N →+ ZMod m), Function.Surjective π ∧
        m = addOrderOf k ∧ ∃ α : ZMod m,
          ∀ x ∈ fourierPositiveHalf A k,
            ∃ q : ℕ, 2 * q < m ∧ π x = α + (q : ZMod m) := by
  obtain ⟨m, hm, π, hπ, hmorder, hchar⟩ :=
    exists_frequency_quotient k hk
  letI : NeZero m := ⟨hm.ne'⟩
  let r : Circle := fourierDirectionCircle A k hF
  obtain ⟨α, hα⟩ := roots_in_rotated_open_semicircle m r
  refine ⟨m, hm, π, hπ, hmorder, α, ?_⟩
  intro x hx
  have harc := positiveHalf_mem_rotated_centeredArc A k hF hx
  rw [← hchar x] at harc
  exact hα (π x) harc

end Erdos336
