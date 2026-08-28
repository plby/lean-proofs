import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarCancellation

/-!
# Unit adjustments of reduced pairs

Multiplying the two entries of a pair by units preserves a displayed
prime-power Bézout relation after adjusting its coefficients. Ring
equivalences also transport the exact cross-product and cancellation
relations needed for an actual reduced meromorphic presentation.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced

section Units

variable {B : Type*} [CommRing B] {p q t : B}

/-- Unit factors on the entries can be absorbed into the coefficients of
an actual prime-power Bézout relation. -/
theorem bezout_prime_power_mul_units
    (hbez : ∃ n : ℕ, ∃ w : Bˣ, ∃ A C : B, A * p + C * q = t ^ n * (w : B))
    (u v : Bˣ) :
    ∃ n : ℕ, ∃ w : Bˣ, ∃ A C : B,
      A * (p * (u : B)) + C * (q * (v : B)) = t ^ n * (w : B) := by
  obtain ⟨n, w, A, C, hrel⟩ := hbez
  refine ⟨n, w, A * (↑u⁻¹ : B), C * (↑v⁻¹ : B), ?_⟩
  have hu : (A * (↑u⁻¹ : B)) * (p * (u : B)) = A * p := by
    calc
      _ = (A * p) * ((↑u⁻¹ : B) * (u : B)) := by ring
      _ = A * p := by rw [u.inv_mul, mul_one]
  have hv : (C * (↑v⁻¹ : B)) * (q * (v : B)) = C * q := by
    calc
      _ = (C * q) * ((↑v⁻¹ : B) * (v : B)) := by ring
      _ = C * q := by rw [v.inv_mul, mul_one]
  rw [hu, hv]
  exact hrel

end Units

section Transport

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Pulling a reduced pair back through a ring equivalence preserves
nonvanishing, its exact fraction cross-product, and its cancellation law. -/
theorem reduced_pair_relations_transport (e : A ≃+* B) (p q : A) (a b : B)
    (hb : b ≠ 0) (hpq : e p * b = e q * a)
    (hcancel : ∀ h : B, b ∣ h * a ↔ b ∣ h) :
    e.symm b ≠ 0 ∧ p * e.symm b = q * e.symm a ∧
      ∀ h : A, e.symm b ∣ h * e.symm a ↔ e.symm b ∣ h := by
  refine ⟨by simpa using hb, ?_, ?_⟩
  · apply e.injective
    simpa only [map_mul, RingEquiv.apply_symm_apply] using hpq
  · intro h
    calc
      e.symm b ∣ h * e.symm a ↔ b ∣ e h * a := by
        simpa only [map_mul, RingEquiv.apply_symm_apply] using
          (map_dvd_iff e (a := e.symm b) (b := h * e.symm a)).symm
      _ ↔ b ∣ e h := hcancel (e h)
      _ ↔ e.symm b ∣ h := by
        simpa only [RingEquiv.apply_symm_apply] using
          (map_dvd_iff e (a := e.symm b) (b := h))

end Transport

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarReduced
