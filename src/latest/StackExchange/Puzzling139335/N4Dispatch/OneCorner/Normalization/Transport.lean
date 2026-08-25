import StackExchange.Puzzling139335.N4Dispatch.DoublePair.Normalize.Transport

/-!
# Transport with piece labels fixed to their square corners

The isometry acts on every actual piece. Its induced corner permutation
then relabels the pieces so that each label again agrees with its square
corner. The actual pair isometry is changed by conjugation.
-/

open Set

namespace Puzzling139335.N4Dispatch.OneCorner.Normalization

open SquareSymmetry DoublePair.Normalize

noncomputable section

/-- Change coordinates and then restore the labels prescribed by the corners. -/
def reoriented (d : SquareDissection) (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' unitSquare = unitSquare) : SquareDissection :=
  (d.map g hg).reindex (cornerPermutation g hg.subset).symm

@[simp] theorem reoriented_hasProtectedCenter (d : SquareDissection)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' unitSquare = unitSquare) :
    (reoriented d g hg).HasProtectedCenter ↔ d.HasProtectedCenter := by
  simp only [reoriented, SquareDissection.reindex_hasProtectedCenter,
    SquareDissection.map_hasProtectedCenter]

/-- The corner-label condition survives a common square isometry. -/
theorem reoriented_corners (d : SquareDissection)
    (hcorners : ∀ j i, corner j ∈ d.piece i ↔ j = i)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' unitSquare = unitSquare) :
    ∀ j i, corner j ∈ (reoriented d g hg).piece i ↔ j = i := by
  let σ := cornerPermutation g hg.subset
  intro j i
  have hgj : g (corner (σ.symm j)) = corner j := by
    simpa only [σ, Equiv.apply_symm_apply] using
      cornerPermutation_apply g hg.subset (σ.symm j)
  change corner j ∈ g '' d.piece (σ.symm i) ↔ j = i
  rw [← hgj, g.injective.mem_set_image, hcorners]
  exact σ.symm.injective.eq_iff

/-- A piece with old label `a` has the transformed corner as its new label. -/
theorem reoriented_piece_at_permuted_corner (d : SquareDissection)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' unitSquare = unitSquare) (a : Fin 4) :
    (reoriented d g hg).piece (cornerPermutation g hg.subset a) =
      g '' d.piece a := by
  change g '' d.piece ((cornerPermutation g hg.subset).symm
    (cornerPermutation g hg.subset a)) = g '' d.piece a
  rw [Equiv.symm_apply_apply]

theorem reoriented_piece_of_corner_image (d : SquareDissection)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' unitSquare = unitSquare)
    {a b : Fin 4} (hab : g (corner a) = corner b) :
    (reoriented d g hg).piece b = g '' d.piece a := by
  have hindex : cornerPermutation g hg.subset a = b :=
    corner_injective ((cornerPermutation_apply g hg.subset a).symm.trans hab)
  rw [← hindex]
  exact reoriented_piece_at_permuted_corner d g hg a

/-- For pieces labeled by their unique corners, any actual square-preserving
congruence between two pieces takes their labeled corners to each other. -/
theorem pair_maps_owned_corner (d : SquareDissection)
    (hcorners : ∀ j i, corner j ∈ d.piece i ↔ j = i)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heS : e '' unitSquare = unitSquare)
    {a b : Fin 4} (he : e '' d.piece a = d.piece b) :
    e (corner a) = corner b := by
  obtain ⟨c, hce⟩ := maps_corner_of_maps_square_into_square e heS.subset a
  have ha : corner a ∈ d.piece a := (hcorners a a).mpr rfl
  have hm : e (corner a) ∈ d.piece b := he ▸ mem_image_of_mem e ha
  have hcb : c = b := (hcorners c b).mp (hce ▸ hm)
  exact hce.trans (congrArg corner hcb)

/-- Conjugating by a square symmetry cannot turn a different isometry into
the central half-turn: the half-turn commutes with that coordinate change. -/
theorem conjugate_eq_center_reflection_iff (g e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' unitSquare = unitSquare) :
    conjugate g e = AffineIsometryEquiv.pointReflection ℝ squareCenter ↔
      e = AffineIsometryEquiv.pointReflection ℝ squareCenter := by
  constructor
  · intro he
    apply AffineIsometryEquiv.ext
    intro p
    apply g.injective
    have hp := congrArg (fun f : Plane ≃ᵃⁱ[ℝ] Plane => f (g p)) he
    simpa only [conjugate_apply, g.symm_apply_apply,
      ← map_commutes_center_reflection g hg p] using hp
  · rintro rfl
    apply AffineIsometryEquiv.ext
    intro p
    rw [conjugate_apply, map_commutes_center_reflection g hg, g.apply_symm_apply]

/-- The exclusion of actual half-turn-related pairs survives both coordinate
change and corner relabeling. -/
theorem no_center_reflection_pair_reoriented (d : SquareDissection)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hg : g '' unitSquare = unitSquare)
    (hno : ∀ i j, i ≠ j →
      AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece i ≠ d.piece j) :
    ∀ i j, i ≠ j →
      AffineIsometryEquiv.pointReflection ℝ squareCenter ''
        (reoriented d g hg).piece i ≠ (reoriented d g hg).piece j := by
  let σ := cornerPermutation g hg.subset
  intro i j hij
  exact no_center_reflection_pair_map d g hg
    (hno (σ.symm i) (σ.symm j) (σ.symm.injective.ne hij))

end

end Puzzling139335.N4Dispatch.OneCorner.Normalization
