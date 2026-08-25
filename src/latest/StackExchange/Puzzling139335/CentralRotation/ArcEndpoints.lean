import StackExchange.Puzzling139335.JordanTransport
import Wikipedia.SchoenfliesTheorem.ArcMonotone

/-! # Endpoint permutation of an invariant simple arc -/

open Set unitInterval

namespace Schoenflies.IsArcBetween

/-- A homeomorphism preserving a simple arc either fixes its two endpoints
or interchanges them. -/
theorem endpoints_fixed_or_swapped {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (e : Plane ≃ₜ Plane) (he : e '' A = A) :
    (e p = p ∧ e q = q) ∨ (e p = q ∧ e q = p) := by
  obtain ⟨f, hfc, hfi, hfA, hf0, hf1⟩ := hA
  have hmatch : ArcMatch f f e :=
    ⟨hfc, hfi, hfc, hfi, e.continuous.continuousOn, e.injective.injOn,
      by simpa only [hfA] using he⟩
  let φ := transferParam f f e
  have hφ0 : φ 0 ∈ I := hmatch.param_mem_I zero_mem_I
  have hφ1 : φ 1 ∈ I := hmatch.param_mem_I one_mem_I
  obtain ⟨s, hs, hs0⟩ := hmatch.surjOn_param zero_mem_I
  obtain ⟨t, ht, ht1⟩ := hmatch.surjOn_param one_mem_I
  change φ s = 0 at hs0
  change φ t = 1 at ht1
  rcases hmatch.strictMonoOn_or_strictAntiOn_param with hm | hm
  · have h0 : φ 0 = 0 := by
      apply le_antisymm _ hφ0.1
      calc φ 0 ≤ φ s := hm.monotoneOn zero_mem_I hs hs.1
           _ = 0 := hs0
    have h1 : φ 1 = 1 := by
      apply le_antisymm hφ1.2
      calc 1 = φ t := ht1.symm
           _ ≤ φ 1 := hm.monotoneOn ht one_mem_I ht.2
    left
    constructor
    · simpa only [h0, hf0] using
        (show e (f 0) = f (φ 0) from (hmatch.apply_param zero_mem_I).symm)
    · simpa only [h1, hf1] using
        (show e (f 1) = f (φ 1) from (hmatch.apply_param one_mem_I).symm)
  · have h0 : φ 0 = 1 := by
      apply le_antisymm hφ0.2
      calc 1 = φ t := ht1.symm
           _ ≤ φ 0 := hm.antitoneOn zero_mem_I ht ht.1
    have h1 : φ 1 = 0 := by
      apply le_antisymm _ hφ1.1
      calc φ 1 ≤ φ s := hm.antitoneOn hs one_mem_I hs.2
           _ = 0 := hs0
    right
    constructor
    · simpa only [h0, hf0, hf1] using
        (show e (f 0) = f (φ 0) from (hmatch.apply_param zero_mem_I).symm)
    · simpa only [h1, hf0, hf1] using
        (show e (f 1) = f (φ 1) from (hmatch.apply_param one_mem_I).symm)

end Schoenflies.IsArcBetween
