import StackExchange.Puzzling139335.QuarterTurnTopology
import StackExchange.Puzzling139335.PackingMass
import StackExchange.Puzzling139335.Basic

/-!
# An actual quarter-turn pair excludes a protected center

The topological separation theorem produces four interior-disjoint copies.
Their weighted masses saturate the square, so their actual union is the
square. A protected center in the original dissection would be absent from
every copy, a contradiction.
-/

open Set

namespace Puzzling139335.SquareDissection

open QuarterTurnTopology

/-- Either orientation of an actual quarter-turn about the square center
is impossible between two pieces of a protected-center dissection. -/
theorem not_hasProtectedCenter_of_quarterTurn_pair (d : SquareDissection)
    {i j : Fin 4} (hij : i ≠ j) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hsquare : ∀ x, e (e x) = AffineIsometryEquiv.pointReflection ℝ squareCenter x)
    (heS : e '' unitSquare ⊆ unitSquare)
    (he : e '' d.piece i = d.piece j) : ¬ d.HasProtectedCenter := by
  have hfix : e squareCenter = squareCenter :=
    fixed_center e.toHomeomorph hsquare
  have hadj : Disjoint (interior (d.piece i))
      (e.toHomeomorph '' interior (d.piece i)) := by
    change Disjoint (interior (d.piece i)) (e '' interior (d.piece i))
    rw [← interior_image_affineIsometry, he]
    exact d.disjoint_interiors hij
  have horbit := pairwise_disjoint_four_images e.toHomeomorph hsquare
    isOpen_interior (d.jordan i).isConnected_interior.isPreconnected hadj
  let P : Fin 4 → Set Plane := fun n => (e ^ n.val) '' d.piece i
  have hP (n : Fin 4) : IsJordanRegion (P n) :=
    (d.jordan i).image_homeomorph (e ^ n.val).toHomeomorph
  have hdis : Pairwise fun n m => Disjoint (interior (P n)) (interior (P m)) := by
    intro n m hnm
    dsimp only [P]
    rw [interior_image_affineIsometry, interior_image_affineIsometry,
      affineIsometry_pow_image, affineIsometry_pow_image]
    exact horbit hnm
  have hmaps : MapsTo e unitSquare unitSquare :=
    fun x hx => heS (mem_image_of_mem e hx)
  have hsub (n : Fin 4) : P n ⊆ unitSquare := by
    dsimp only [P]
    rw [affineIsometry_pow_image]
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps.iterate n.val (d.piece_subset i hx)
  have hcongr (n : Fin 4) : Congruent (P n) (d.piece i) :=
    Congruent.symm ⟨e ^ n.val, rfl⟩
  have hcover := d.congruent_piece_packing_covers i P hP hdis hsub hcongr
  rintro ⟨k, hk⟩
  have hnoti : squareCenter ∉ interior (d.piece i) :=
    (d.center_not_mem_fixed_pair hij e he hfix).1
  have hki : k ≠ i := by
    rintro rfl
    exact hnoti hk
  have hnot : squareCenter ∉ d.piece i := d.not_mem_other_piece hki hk
  have hnotP (n : Fin 4) : squareCenter ∉ P n := by
    dsimp only [P]
    rw [affineIsometry_pow_image]
    rintro ⟨x, hx, hxeq⟩
    have hfixn : (e : Plane → Plane)^[n.val] squareCenter = squareCenter :=
      Function.iterate_fixed hfix n.val
    have hxcenter : x = squareCenter :=
      (e.injective.iterate n.val) (hxeq.trans hfixn.symm)
    exact hnot (hxcenter ▸ hx)
  have hcunion : squareCenter ∈ ⋃ n, P n := hcover.symm ▸ squareCenter_mem_unitSquare
  obtain ⟨n, hn⟩ := mem_iUnion.mp hcunion
  exact hnotP n hn

end Puzzling139335.SquareDissection
