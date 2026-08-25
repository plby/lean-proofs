import StackExchange.Puzzling139335.N7.FullTypes
import StackExchange.Puzzling139335.SquareSymmetry.CornerPermutation

/-!
# The singleton's corner type after a square symmetry

A square symmetry permutes the physical corners, so any corner of the
transformed single-corner piece pulls back to an actual corner of that
piece.  If the repeated endpoint is a full type, the singleton cannot use
it; its remaining possible types are the common and other endpoints.
-/

open Set

namespace Puzzling139335.N7.PairConfiguration

open N8

noncomputable section

/-- Every physical corner of the mapped singleton comes from one of its
two possible nonfull intrinsic types. -/
theorem singleton_mapped_corner_type {d : SquareDissection}
    (C : PairConfiguration d) (hfull : C.repeatedEnd ∈ N5.fullCornerTypes d)
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hfS : f '' unitSquare = unitSquare)
    {j : Fin 4} (hj : corner j ∈ f '' d.piece C.singleton) :
    f (d.placement C.singleton C.common) = corner j ∨
      f (d.placement C.singleton C.otherEnd) = corner j := by
  classical
  obtain ⟨σ, hσ⟩ := SquareSymmetry.exists_corner_permutation_of_preserves_square f hfS
  have hcorner : f (corner (σ.symm j)) = corner j := by
    simpa only [σ.apply_symm_apply] using hσ (σ.symm j)
  have ha : corner (σ.symm j) ∈ d.piece C.singleton := by
    obtain ⟨x, hx, hxj⟩ := hj
    have hxa : x = corner (σ.symm j) := f.injective (hxj.trans hcorner.symm)
    exact hxa ▸ hx
  have hv : d.intrinsicCorner C.singleton (σ.symm j) ∈
      intrinsicPair d C.singleton :=
    (mem_intrinsicPair d C.singleton _).mpr ⟨σ.symm j, ha, rfl⟩
  have hused := intrinsicPair_subset_usedCornerTypes d C.singleton hv
  rw [C.types] at hused
  simp only [Finset.mem_insert, Finset.mem_singleton] at hused
  have hmap : f (d.placement C.singleton
      (d.intrinsicCorner C.singleton (σ.symm j))) = corner j := by
    rw [d.placement_intrinsicCorner]
    exact hcorner
  rcases hused with hcommon | hrepeated | hother
  · exact Or.inl (hcommon ▸ hmap)
  · exact False.elim (C.singleton_type_not_full hv (hrepeated.symm ▸ hfull))
  · exact Or.inr (hother ▸ hmap)

end

end Puzzling139335.N7.PairConfiguration
