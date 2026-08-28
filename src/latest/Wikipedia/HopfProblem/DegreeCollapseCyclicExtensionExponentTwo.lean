import Wikipedia.HopfProblem.DegreeCollapseCyclicExtensionCharacter

/-!
# The integral structure of an exponent-two cyclic extension

The full quotient character, not just its value on the attaching class,
detects whether the meridian is twice an exterior class. For an exponent-two
quotient, a nonzero character constructs that half-meridian explicitly.
A section with zero character can then be corrected by an integral meridian
multiple to have order at most two. All statements concern the original
extension maps and elements; no abstract splitting is assumed.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
  (μ : G) (q : G →+ H) (hker : q.ker = AddSubgroup.zmultiples μ)
  (h2 : ∀ x : H, (2 : ℤ) • x = 0)

include hker h2 in
theorem exists_double_coefficient (g : G) :
    ∃ k : ℤ, k • μ = (2 : ℤ) • g := by
  have hg : (2 : ℤ) • g ∈ q.ker := by
    change q ((2 : ℤ) • g) = 0
    rw [map_zsmul, h2]
  rw [hker] at hg
  exact AddSubgroup.mem_zmultiples_iff.mp hg

variable [Finite H] (hμ : Injective (fun k : ℤ ↦ k • μ)) (hq : Surjective q)

include h2

theorem exists_half_meridian_of_character_ne_zero
    (hn : ∃ x : H, character μ q hker hμ hq x ≠ 0) :
    ∃ h : G, (2 : ℤ) • h = μ := by
  obtain ⟨x, hx⟩ := hn
  obtain ⟨g, rfl⟩ := hq x
  obtain ⟨k, hk⟩ := exists_double_coefficient μ q hker h2 g
  have hrel : (2 : ℤ) • g + (-k) • μ = 0 := by
    rw [← hk, neg_zsmul, add_neg_cancel]
  have hodd : ¬ (2 : ℤ) ∣ k := by
    intro hd
    apply hx
    exact (character_eq_zero_iff_dvd μ q hker hμ hq g 2 (-k) (by norm_num) hrel).2
      (dvd_neg.mpr hd)
  have hmod : k % 2 = 1 := by
    have hb := Int.emod_nonneg k (by norm_num : (2 : ℤ) ≠ 0)
    have ht := Int.emod_lt_of_pos k (by norm_num : (0 : ℤ) < 2)
    have hn : k % 2 ≠ 0 := fun he ↦ hodd (Int.dvd_of_emod_eq_zero he)
    omega
  refine ⟨g - (k / 2) • μ, ?_⟩
  calc
    (2 : ℤ) • (g - (k / 2) • μ) = (k - 2 * (k / 2)) • μ := by
      rw [smul_sub, ← hk, ← mul_zsmul, sub_zsmul]
      abel
    _ = μ := by
      have he : k - 2 * (k / 2) = 1 := by omega
      rw [he, one_zsmul]

theorem exists_integral_section_coordinate (g : G)
    (hz : character μ q hker hμ hq (q g) = 0) :
    ∃ l : ℤ, (2 : ℤ) • g = (2 * l) • μ := by
  obtain ⟨k, hk⟩ := exists_double_coefficient μ q hker h2 g
  have hrel : (2 : ℤ) • g + (-k) • μ = 0 := by
    rw [← hk, neg_zsmul, add_neg_cancel]
  have hd : (2 : ℤ) ∣ k := dvd_neg.mp
    ((character_eq_zero_iff_dvd μ q hker hμ hq g 2 (-k) (by norm_num) hrel).1 hz)
  obtain ⟨l, hl⟩ := hd
  exact ⟨l, hk.symm.trans (congrArg (fun n : ℤ ↦ n • μ) hl)⟩

theorem exists_torsion_corrected_section (g : G)
    (hz : character μ q hker hμ hq (q g) = 0) :
    ∃ l : ℤ, (2 : ℤ) • (g - l • μ) = 0 ∧ q (g - l • μ) = q g := by
  obtain ⟨l, hl⟩ := exists_integral_section_coordinate μ q hker h2 hμ hq g hz
  have hqμ : q μ = 0 := by
    change μ ∈ q.ker
    rw [hker]
    exact AddSubgroup.mem_zmultiples μ
  refine ⟨l, ?_, ?_⟩
  · rw [smul_sub, hl, ← mul_zsmul, sub_self]
  · rw [map_sub, map_zsmul, hqμ, smul_zero, sub_zero]

theorem exists_even_twist_double_relation (g : G)
    (hz : character μ q hker hμ hq (q g) = 0) :
    ∃ j : ℤ, (2 : ℤ) • (g + (2 * j) • μ) = 0 ∨
      (2 : ℤ) • (g + (2 * j) • μ) = (2 : ℤ) • μ := by
  obtain ⟨l, hl⟩ := exists_integral_section_coordinate μ q hker h2 hμ hq g hz
  have hr : l + 2 * (-(l / 2)) = 0 ∨ l + 2 * (-(l / 2)) = 1 := by omega
  refine ⟨-(l / 2), ?_⟩
  have he : (2 : ℤ) • (g + (2 * (-(l / 2))) • μ) =
      (2 * (l + 2 * (-(l / 2)))) • μ := by
    rw [smul_add, hl, ← mul_zsmul, ← add_zsmul]
    congr 1
    ring
  rcases hr with hr | hr
  · left
    rw [he, hr, mul_zero, zero_zsmul]
  · right
    rw [he, hr, mul_one]

end Wikipedia.HopfProblem.DegreeCollapse.CyclicExtensionCharacter
