import ErdosProblems.Erdos489.RayCapacity

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Primitive covered occurrences of one fixed modulus pair satisfy the
primitive-ray capacity bound, provided quotient pairs distinguish occurrences. -/
theorem fixed_modulus_occurrence_capacity
    (I : Finset ℕ) (u v : ℕ → ℕ) (a b X D : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hX : 0 < X) (hD : 0 < D)
    (hu : ∀ i ∈ I, 0 < u i) (hv : ∀ i ∈ I, 0 < v i)
    (hadu : ∀ i ∈ I, a ∣ u i) (hbdv : ∀ i ∈ I, b ∣ v i)
    (hprimitive : ∀ i ∈ I, Nat.Coprime (u i) (v i))
    (huX : ∀ i ∈ I, u i ≤ X) (hvX : ∀ i ∈ I, v i ≤ X)
    (hne : ∀ i ∈ I, u i ≠ v i)
    (hdist : ∀ i ∈ I, Nat.dist (u i) (v i) ≤ D)
    (hinj : Set.InjOn (fun i => (u i / a, v i / b)) (I : Set ℕ)) :
    a * b * I.card ≤ 4 * X * D + 2 * (a * b) := by
  let q : ℕ → ℕ × ℕ := fun i => (u i / a, v i / b)
  let T := I.image q
  have hcard : T.card = I.card := Finset.card_image_iff.mpr hinj
  have hbound := primitive_covered_two_sided_count_bound T a b X D
    ha hb hX hD
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      apply Nat.div_pos (Nat.le_of_dvd (hu i hi) (hadu i hi)) ha)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      apply Nat.div_pos (Nat.le_of_dvd (hv i hi) (hbdv i hi)) hb)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hprimitive i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi)] using huX i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hbdv i hi)] using hvX i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hne i hi)
    (fun z hz => by
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      dsimp [q]
      simpa [Nat.mul_div_cancel' (hadu i hi),
        Nat.mul_div_cancel' (hbdv i hi)] using hdist i hi)
  rwa [hcard] at hbound

end Erdos489
