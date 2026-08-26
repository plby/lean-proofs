import ErdosProblems.Erdos941.HurwitzOrder

/-! # Doubled coordinates in the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

theorem hurwitz_mem_iff_half_coordinates (q : ℍ[ℚ]) :
    q ∈ hurwitzOrder ↔ ∃ a b c d : ℤ,
      q = ⟨(a : ℚ) / 2, (b : ℚ) / 2, (c : ℚ) / 2, (d : ℚ) / 2⟩ ∧
      a % 2 = d % 2 ∧ b % 2 = d % 2 ∧ c % 2 = d % 2 := by
  constructor
  · rintro ⟨a, b, c, d, rfl⟩
    refine ⟨2 * a + d, 2 * b + d, 2 * c + d, d, ?_, ?_, ?_, ?_⟩
    · apply Quaternion.ext <;> dsimp [hurwitzCoordinates] <;> push_cast <;> ring
    all_goals omega
  · rintro ⟨a, b, c, d, rfl, ha, hb, hc⟩
    have ha' : 2 ∣ a - d := by omega
    have hb' : 2 ∣ b - d := by omega
    have hc' : 2 ∣ c - d := by omega
    obtain ⟨x, hx⟩ := ha'
    obtain ⟨y, hy⟩ := hb'
    obtain ⟨z, hz⟩ := hc'
    refine ⟨x, y, z, d, ?_⟩
    have hx' : (a : ℚ) - d = 2 * x := by exact_mod_cast hx
    have hy' : (b : ℚ) - d = 2 * y := by exact_mod_cast hy
    have hz' : (c : ℚ) - d = 2 * z := by exact_mod_cast hz
    apply Quaternion.ext <;> dsimp [hurwitzCoordinates]
    · linarith
    · linarith
    · linarith

end Erdos941
