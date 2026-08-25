import StackExchange.Puzzling139335.QuarterTurnPair
import StackExchange.Puzzling139335.SymmetryOrbit.Classification
import StackExchange.Puzzling139335.SymmetryOrbit.Commuting
import StackExchange.Puzzling139335.SymmetryOrbit.Saturation

/-!
# Three actual square-symmetry copies exclude a protected center

Among three placements in one square-symmetry orbit, a pair differs by a
quarter-turn or the placements extend to the orbit of two commuting
involutions. The quarter-turn obstruction handles the first case. In the
second case the four orbit copies have disjoint interiors and their
weighted masses force them to cover the square.

Only the displayed congruences between actual pieces are used. The proof
does not assume that a symmetry permutes all the original pieces.
-/

open Set

namespace Puzzling139335.SquareDissection

open SymmetryOrbit

/-- Three distinct actual pieces cannot be square-symmetry images of one
of them in a dissection with a protected center. -/
theorem not_hasProtectedCenter_of_three_square_symmetry_copies (d : SquareDissection)
    {i j k : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (e f : Plane ≃ᵃⁱ[ℝ] Plane)
    (heS : e '' unitSquare ⊆ unitSquare) (hfS : f '' unitSquare ⊆ unitSquare)
    (he : e '' d.piece i = d.piece j) (hf : f '' d.piece i = d.piece k) :
    ¬ d.HasProtectedCenter := by
  rcases square_symmetry_pair_classification e f heS hfS with
    hequarter | hfquarter | ⟨heinvol, hfinvol, hcomposite | hcomm⟩
  · exact d.not_hasProtectedCenter_of_quarterTurn_pair hij e hequarter heS he
  · exact d.not_hasProtectedCenter_of_quarterTurn_pair hik f hfquarter hfS hf
  · have hefS : (e.trans f) '' unitSquare ⊆ unitSquare := by
      rintro _ ⟨x, hx, rfl⟩
      exact hfS ⟨e x, heS ⟨x, hx, rfl⟩, rfl⟩
    have hef : (e.trans f) '' d.piece j = d.piece k := by
      calc
        (e.trans f) '' d.piece j = (e.trans f) '' (e '' d.piece i) := by rw [he]
        _ = f '' d.piece i := by
          simp only [image_image, AffineIsometryEquiv.coe_trans,
            Function.comp_apply]
          congr 1
          funext x
          rw [heinvol x]
        _ = d.piece k := hf
    exact d.not_hasProtectedCenter_of_quarterTurn_pair hjk (e.trans f)
      hcomposite hefS hef
  · have hdis := pairwise_disjoint_commutingOrbit heinvol hfinvol hcomm
      (P := d.piece i)
      (by simpa only [he] using d.disjoint_interiors hij)
      (by simpa only [hf] using d.disjoint_interiors hik)
      (by simpa only [he, hf] using d.disjoint_interiors hjk)
    apply d.not_hasProtectedCenter_of_square_symmetry_packing hij e he
      (SquareSymmetry.center_fixed_of_maps_square_into_square e heS)
      (commutingPlacements e f)
    · intro n
      rw [commutingPlacements_image]
      exact commutingOrbit_subset (Subset.refl unitSquare) heS hfS n
    · intro n m hnm
      simpa only [commutingPlacements_image] using hdis hnm

/-- The same obstruction when three placements are specified from an
arbitrary common prototype, rather than from one of the three pieces. -/
theorem not_hasProtectedCenter_of_three_square_orbit_images (d : SquareDissection)
    (P : Set Plane) (a : Fin 3 → Fin 4) (ha : Function.Injective a)
    (g : Fin 3 → Plane ≃ᵃⁱ[ℝ] Plane)
    (hgS : ∀ n, g n '' unitSquare ⊆ unitSquare)
    (hg : ∀ n, g n '' P = d.piece (a n)) : ¬ d.HasProtectedCenter := by
  have hS₀ : g 0 '' unitSquare = unitSquare :=
    SquareSymmetry.preserves_square_of_maps_square_into_square (g 0) (hgS 0)
  have hS₀inv : (g 0).symm '' unitSquare ⊆ unitSquare := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ g 0 '' unitSquare := hS₀.symm ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    simpa only [AffineIsometryEquiv.symm_apply_apply] using hy
  have hrelativeS (n : Fin 3) :
      ((g 0).symm.trans (g n)) '' unitSquare ⊆ unitSquare := by
    rintro _ ⟨x, hx, rfl⟩
    exact hgS n ⟨(g 0).symm x, hS₀inv ⟨x, hx, rfl⟩, rfl⟩
  have hrelative (n : Fin 3) :
      ((g 0).symm.trans (g n)) '' d.piece (a 0) = d.piece (a n) := by
    calc
      ((g 0).symm.trans (g n)) '' d.piece (a 0) =
          ((g 0).symm.trans (g n)) '' (g 0 '' P) := by rw [hg 0]
      _ = g n '' P := by
        simp only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_apply,
          AffineIsometryEquiv.symm_apply_apply]
      _ = d.piece (a n) := hg n
  exact d.not_hasProtectedCenter_of_three_square_symmetry_copies
    (ha.ne (by decide : (0 : Fin 3) ≠ 1))
    (ha.ne (by decide : (0 : Fin 3) ≠ 2))
    (ha.ne (by decide : (1 : Fin 3) ≠ 2))
    ((g 0).symm.trans (g 1)) ((g 0).symm.trans (g 2))
    (hrelativeS 1) (hrelativeS 2) (hrelative 1) (hrelative 2)

end Puzzling139335.SquareDissection
