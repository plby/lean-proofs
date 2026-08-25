import StackExchange.Puzzling139335.FourIncidences
import StackExchange.Puzzling139335.SymmetryOrbit

/-!
# At least three types in the one-corner-per-piece case

The center piece has an unrepeated type. If there were at most two types,
the other three pieces would all use the second type and would form a
forbidden square-symmetry orbit. This is a direct consequence of actual
corner ownership and the proved three-copy obstruction.
-/

open Set

namespace Puzzling139335

private theorem three_le_card_image_of_unique_fiber {α : Type*} [DecidableEq α]
    (f : Fin 4 → α) (i : Fin 4)
    (hunique : ∀ j, f j = f i → j = i)
    (htriple : ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
      f a = f b → f a = f c → False) :
    3 ≤ (Finset.univ.image f).card := by
  classical
  by_contra hcard
  have hle : (Finset.univ.image f).card ≤ 2 := by omega
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have hσ0 : σ 0 = i := by simp [σ]
  have hne (k : Fin 4) (hk : k ≠ 0) : f (σ k) ≠ f i := by
    intro h
    exact hk (σ.injective ((hunique (σ k) h).trans hσ0.symm))
  have hpair : ({f i, f (σ 1)} : Finset α) ⊆ Finset.univ.image f := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · rw [Finset.mem_singleton] at hx
      exact hx ▸ Finset.mem_image.mpr ⟨σ 1, Finset.mem_univ _, rfl⟩
  have heq : Finset.univ.image f = {f i, f (σ 1)} := by
    apply (Finset.eq_of_subset_of_card_le hpair ?_).symm
    simpa [Ne.symm (hne 1 (by decide))] using hle
  have hother (k : Fin 4) (hk : k ≠ 0) : f (σ k) = f (σ 1) := by
    have hm : f (σ k) ∈ Finset.univ.image f :=
      Finset.mem_image.mpr ⟨σ k, Finset.mem_univ _, rfl⟩
    rw [heq] at hm
    have hm' : f (σ k) = f i ∨ f (σ k) = f (σ 1) := by simpa using hm
    exact hm'.resolve_left (hne k hk)
  apply htriple (σ 1) (σ 2) (σ 3)
  · exact fun h => (by decide : (1 : Fin 4) ≠ 2) (σ.injective h)
  · exact fun h => (by decide : (1 : Fin 4) ≠ 3) (σ.injective h)
  · exact fun h => (by decide : (2 : Fin 4) ≠ 3) (σ.injective h)
  · exact (hother 2 (by decide)).symm
  · exact (hother 3 (by decide)).symm

namespace SquareDissection

/-- In the four-incidence case, if every piece owns a corner, a putative
counterexample uses at least three intrinsic types. -/
theorem three_le_usedCornerTypes_card_of_four_incidences (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    (hcorners : ∀ i, ∃ j, corner j ∈ d.piece i) :
    3 ≤ d.usedCornerTypes.card := by
  classical
  choose a ha using hcorners
  let f : Fin 4 → Plane := fun i => d.intrinsicCorner i (a i)
  obtain ⟨i, hi⟩ := hc
  have hunique : ∀ j, f j = f i → j = i := by
    intro j h
    exact d.center_owner_type_unique_of_four_incidences hN hi (ha i) h.symm
  have htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      f j = f k → f j = f l → False := by
    intro j k l hjk hjl hkl hjkt hjlt
    have hsource := d.unique_corner_owner_of_four_incidences hN (ha j)
    exact d.not_hasProtectedCenter_of_three_square_symmetry_copies hjk hjl hkl
      (d.relativePlacement j k) (d.relativePlacement j l)
      (d.relativePlacement_preserves_square_of_unique_corner hsource hjkt).subset
      (d.relativePlacement_preserves_square_of_unique_corner hsource hjlt).subset
      (d.relativePlacement_image j k) (d.relativePlacement_image j l) ⟨i, hi⟩
  have hsubset : Finset.univ.image f ⊆ d.usedCornerTypes := by
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    exact d.mem_usedCornerTypes.mpr ⟨j, a j, ha j, rfl⟩
  exact (three_le_card_image_of_unique_fiber f i hunique htriple).trans
    (Finset.card_le_card hsubset)

theorem usedCornerTypes_card_eq_three_of_four_incidences (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    (hcorners : ∀ i, ∃ j, corner j ∈ d.piece i)
    (hnotRect : ¬ HasRectangularHull (d.piece 0)) :
    d.usedCornerTypes.card = 3 :=
  le_antisymm (d.usedCornerTypes_card_le_three_of_not_rectangular hnotRect)
    (d.three_le_usedCornerTypes_card_of_four_incidences hc hN hcorners)

end SquareDissection

end Puzzling139335
