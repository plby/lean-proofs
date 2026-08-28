import Wikipedia.HopfProblem.DegreeCollapseCyclicSurgeryIndex

/-!
# Centering the torsion coefficient by an even framing adjustment

If l does not divide p, subtracting a suitable even multiple of l makes
the coefficient nonzero and strictly smaller in absolute value than l.
Combined with the genuine cyclic-index formula, this gives a strict
decrease for the corresponding quotient of the same abelian group.
The divisible case is deliberately excluded, not treated as a unit case.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex

theorem centered_even_remainder (l p : ℤ) (hl : 0 < l) :
    ∃ j : ℤ, -l ≤ p - 2 * l * j ∧ p - 2 * l * j < l := by
  let j := (p + l) / (2 * l)
  have hn : 2 * l ≠ 0 := by omega
  have hpos : 0 < 2 * l := by omega
  have h0 := Int.emod_nonneg (p + l) hn
  have h1 := Int.emod_lt_of_pos (p + l) hpos
  have he := Int.emod_add_mul_ediv (p + l) (2 * l)
  refine ⟨j, ?_, ?_⟩ <;> dsimp [j] <;> omega

theorem strict_even_remainder (l p : ℤ) (hl : 0 < l) (hp : ¬ l ∣ p) :
    ∃ j : ℤ, p - 2 * l * j ≠ 0 ∧ (p - 2 * l * j).natAbs < l.natAbs := by
  obtain ⟨j, hlo, hhi⟩ := centered_even_remainder l p hl
  have hne : p - 2 * l * j ≠ 0 := by
    intro h
    apply hp
    refine ⟨2 * j, ?_⟩
    nlinarith
  have hlo' : -l < p - 2 * l * j := by
    by_contra h
    have he : p - 2 * l * j = -l := le_antisymm (le_of_not_gt h) hlo
    apply hp
    refine ⟨2 * j - 1, ?_⟩
    nlinarith
  refine ⟨j, hne, ?_⟩
  have ha : |p - 2 * l * j| < |l| := by
    rw [abs_of_pos hl]
    exact abs_lt.mpr ⟨hlo', hhi⟩
  have hc : ((p - 2 * l * j).natAbs : ℤ) < (l.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hc

theorem exists_strict_even_quotient {G : Type*} [AddCommGroup G] (ε μ : G)
    (hμ : Function.Injective (fun k : ℤ ↦ k • μ)) (l p : ℤ) (hl : 0 < l)
    (hp : ¬ l ∣ p) (h : l • ε + p • μ = 0) (hfinite : (AddSubgroup.zmultiples μ).index ≠ 0) :
    ∃ j : ℤ, (AddSubgroup.zmultiples (ε + (2 * j) • μ)).index ≠ 0 ∧
      (AddSubgroup.zmultiples (ε + (2 * j) • μ)).index < (AddSubgroup.zmultiples μ).index := by
  obtain ⟨j, hne, hsmall⟩ := strict_even_remainder l p hl hp
  refine ⟨j, strict_index_decrease (ε + (2 * j) • μ) μ hμ l
    (p - 2 * l * j) hne hsmall ?_ hfinite⟩
  calc
    l • (ε + (2 * j) • μ) + (p - 2 * l * j) • μ = l • ε + p • μ := by
      rw [zsmul_add, sub_zsmul]
      have he : l • ((2 * j) • μ) = (2 * l * j) • μ := by
        rw [← mul_zsmul]
        congr 1
        ring
      rw [he]
      abel
    _ = 0 := h

end Wikipedia.HopfProblem.DegreeCollapse.CyclicSurgeryIndex
