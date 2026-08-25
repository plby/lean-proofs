import StackExchange.Puzzling139335.SquareSymmetry.CornerRigidity
import StackExchange.Puzzling139335.SquareSymmetry.CornerPermutation

/-!
# Exhaustive coordinate forms of square symmetries

The four coordinate reflections, with optional coordinate interchange,
are all Euclidean congruences that take the square into itself. The
classification is deduced from the set inclusion, not assumed.
-/

open Set Metric

namespace Puzzling139335.SquareSymmetry

noncomputable section

theorem coordinate_forms_of_maps_square_into_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare ⊆ unitSquare) :
    ∃ b : Fin 4,
      (∀ p, e p = cornerFlip b p) ∨
      (∀ p, e p = cornerFlip b (!₂[p 1, p 0] : Plane)) := by
  obtain ⟨b, hb⟩ := maps_corner_of_maps_square_into_square e he 0
  have hcorner0 : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have he0 : e 0 = corner b := by rwa [hcorner0] at hb
  let g := e.trans (cornerFlip b)
  have hg0 : g 0 = 0 := by
    change cornerFlip b (e 0) = 0
    rw [he0, cornerFlip_corner]
  have hglocal : g '' (ball 0 1 ∩ unitSquare) ⊆ unitSquare := by
    rintro _ ⟨p, hp, rfl⟩
    exact (cornerFlip_mem_unitSquare b).mpr (he (mem_image_of_mem e hp.2))
  have hrecover (p : Plane) : e p = cornerFlip b (g p) := by
    change e p = cornerFlip b (cornerFlip b (e p))
    rw [cornerFlip_involutive]
  refine ⟨b, ?_⟩
  rcases coordinate_form_of_origin_neighborhood g hg0 (by norm_num) hglocal with hid | hswap
  · exact Or.inl fun p => (hrecover p).trans (congrArg (cornerFlip b) (hid p))
  · exact Or.inr fun p => (hrecover p).trans (congrArg (cornerFlip b) (hswap p))

/-- Isometric inclusion of the square is necessarily equality. -/
theorem preserves_square_of_maps_square_into_square
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' unitSquare ⊆ unitSquare) :
    e '' unitSquare = unitSquare := by
  obtain ⟨b, hform | hform⟩ := coordinate_forms_of_maps_square_into_square e he
  · simpa only [hform] using cornerFlip_image_unitSquare b
  · apply Subset.antisymm he
    intro p hp
    let q := cornerFlip b p
    refine ⟨!₂[q 1, q 0], ?_, ?_⟩
    · have hq : q ∈ unitSquare := (cornerFlip_mem_unitSquare b).mpr hp
      exact ⟨hq.2, hq.1⟩
    · rw [hform]
      have hswap : (!₂[(!₂[q 1, q 0] : Plane) 1,
          (!₂[q 1, q 0] : Plane) 0] : Plane) = q := by
        ext i
        fin_cases i <;> rfl
      rw [hswap]
      exact cornerFlip_involutive b p

end

end Puzzling139335.SquareSymmetry
