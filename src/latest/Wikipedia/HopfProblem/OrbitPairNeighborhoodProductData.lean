import Wikipedia.HopfProblem.OrbitPairNeighborhoodProductMotion

/-!
# Neighborhood deformation and homotopy extension for a product-boundary union

The product of the heights has exactly the required zero set. At time
one, the factor with smaller nonzero height has completed its deformation
and lies in the included subspace. Together with exact stationarity this
gives neighborhood deformation data for the literal union inclusion.
-/

noncomputable section

universe u v

open CategoryTheory unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct

open NeighborhoodDeformation

variable {A X : TopCat.{u}} {B Y : TopCat.{v}} {i : A ⟶ X} {j : B ⟶ Y}
    (D : Data i) (E : Data j)

theorem height_zero_iff (p : X × Y) : height D E p = 0 ↔ p ∈ boundary i j := by
  constructor
  · intro hp
    have h : (D.height p.1 : ℝ) * (E.height p.2 : ℝ) = 0 := congrArg Subtype.val hp
    rcases mul_eq_zero.mp h with hx | hy
    · exact Or.inl ((D.zero_iff _).mp (Subtype.ext hx))
    · exact Or.inr ((E.zero_iff _).mp (Subtype.ext hy))
  · intro hp
    change D.height p.1 * E.height p.2 = 0
    rcases hp with hx | hy
    · rw [(D.zero_iff _).mpr hx, zero_mul]
    · rw [(E.zero_iff _).mpr hy, mul_zero]

theorem deformation_terminal (p : X × Y) (hp : height D E p < 1) :
    deformation D E (1, p) ∈ boundary i j := by
  rcases p with ⟨x, y⟩
  by_cases hx : D.height x = 0
  · rw [deformation_fixed_left D E 1 x y hx]
    exact Or.inl ((D.zero_iff _).mp hx)
  · by_cases hy : E.height y = 0
    · rw [deformation_fixed_right D E 1 x y hy]
      exact Or.inr ((E.zero_iff _).mp hy)
    · change D.height x * E.height y < 1 at hp
      rcases le_total (D.height x) (E.height y) with hxy | hyx
      · left
        change D.deformation (1 * ratio (D.height x) (E.height y), x) ∈ Set.range i
        rw [ratio_of_le _ _ hxy hy, one_mul]
        exact D.terminal x (smaller_lt_one _ _ hxy hp)
      · right
        change E.deformation (1 * ratio (E.height y) (D.height x), y) ∈ Set.range j
        rw [ratio_of_le _ _ hyx hx, one_mul]
        exact E.terminal y (smaller_lt_one _ _ hyx (by simpa only [mul_comm] using hp))

def data : Data (inclusion i j) where
  height := height D E
  deformation := deformation D E
  zero_iff p := by
    rw [range_inclusion]
    exact height_zero_iff D E p
  bottom := deformation_bottom D E
  fixed t p := deformation_fixed D E t p.val p.property
  terminal p hp := ⟨⟨deformation D E (1, p), deformation_terminal D E p hp⟩, rfl⟩

include D E in
theorem hasHomotopyExtension : HomotopyExtension.HasHomotopyExtension (inclusion i j) :=
  NeighborhoodDeformation.hasHomotopyExtension (data D E) IsEmbedding.subtypeVal

theorem of_closed_homotopyExtension (hi : HomotopyExtension.HasHomotopyExtension i)
    (hj : HomotopyExtension.HasHomotopyExtension j)
    (hci : IsClosedEmbedding i) (hcj : IsClosedEmbedding j) :
    HomotopyExtension.HasHomotopyExtension (inclusion i j) := by
  obtain ⟨D⟩ := NeighborhoodDeformation.exists_data i hi hci
  obtain ⟨E⟩ := NeighborhoodDeformation.exists_data j hj hcj
  exact hasHomotopyExtension D E

theorem realized_mono_product_boundary {S T : SSet.{u}} (f : S ⟶ T) [Mono f]
    {U V : SSet.{v}} (g : U ⟶ V) [Mono g] (n m : ℕ)
    [T.HasDimensionLT n] [V.HasDimensionLT m] :
    HomotopyExtension.HasHomotopyExtension (inclusion (SSet.toTop.map f) (SSet.toTop.map g)) :=
  of_closed_homotopyExtension (HomotopyExtension.realized_mono_of_dimension f n)
    (HomotopyExtension.realized_mono_of_dimension g m)
    (RealizationSimplex.realizedMono_isClosedEmbedding f)
    (RealizationSimplex.realizedMono_isClosedEmbedding g)

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct
