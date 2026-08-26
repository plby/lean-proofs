import ErdosProblems.Erdos633.OneTwentyGrid

/-!
# Stacking slanted trapezoid rows

The rows are translated by vectors in the 60-degree direction in the physical
plane. Coverage includes their boundaries; disjointness uses horizontal
separating lines in hexagonal coordinates.
-/

namespace Erdos633

def trapezoidRow (H : ℝ) (m : ℕ) (j : Fin m) : Set ℂ :=
  {z | 0 ≤ z.re ∧ (j : ℝ) * H ≤ z.im ∧ z.im ≤ ((j : ℝ) + 1) * H ∧
    z.re + z.im ≤ 2 * m * H}

theorem trapezoidRows_cover (H : ℝ) (hH : 0 < H) (m : ℕ) (hm : 0 < m) :
    (⋃ j : Fin m, trapezoidRow H m j) = slantedTrapezoid ((m : ℝ) * H) (2 * m * H) := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    have hj0 : (0 : ℝ) ≤ j := by positivity
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.add_one_le_iff.mpr j.isLt
    exact ⟨hj.1, by nlinarith [hj.2.1], by nlinarith [hj.2.2.1], hj.2.2.2⟩
  · intro hz
    have hy0 : 0 ≤ z.im / H := div_nonneg hz.2.1 hH.le
    have hym : z.im / H ≤ m := (div_le_iff₀ hH).mpr hz.2.2.1
    obtain ⟨j, hj, hj1, _⟩ := exists_unit_interval_index m hm (z.im / H) hy0 hym
    refine Set.mem_iUnion.mpr ⟨j, hz.1, ?_, ?_, hz.2.2.2⟩
    · exact (le_div_iff₀ hH).mp hj
    · exact (div_le_iff₀ hH).mp hj1

theorem trapezoidRows_disjoint (H : ℝ) (hH : 0 < H) (m : ℕ) :
    Pairwise fun i j : Fin m =>
      Disjoint (interior (trapezoidRow H m i)) (interior (trapezoidRow H m j)) := by
  have hsep (i j : Fin m) (hij : i < j) :
      Disjoint (interior (trapezoidRow H m i)) (interior (trapezoidRow H m j)) := by
    have hijR : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.add_one_le_iff.mpr hij
    apply separated_interiors Complex.imCLM (fun r => ⟨⟨0, r⟩, rfl⟩) ((j : ℝ) * H)
    · intro z hz
      change z.im ≤ (j : ℝ) * H
      nlinarith [hz.2.2.1]
    · exact fun _ hz => hz.2.1
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hsep i j h
  · exact (hsep j i h).symm

theorem trapezoidRow_translate (H : ℝ) (m : ℕ) (j : Fin m) :
    (fun z : ℂ => z + (⟨0, (j : ℝ) * H⟩ : ℂ)) ''
      slantedTrapezoid H ((2 * m - (j : ℝ)) * H) = trapezoidRow H m j := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change 0 ≤ w.re + 0 ∧ (j : ℝ) * H ≤ w.im + (j : ℝ) * H ∧
      w.im + (j : ℝ) * H ≤ ((j : ℝ) + 1) * H ∧
      (w.re + 0) + (w.im + (j : ℝ) * H) ≤ 2 * m * H
    exact ⟨by linarith [hw.1], by linarith [hw.2.1],
      by nlinarith [hw.2.2.1], by nlinarith [hw.2.2.2]⟩
  · intro hz
    refine ⟨⟨z.re, z.im - (j : ℝ) * H⟩, ?_, ?_⟩
    · change 0 ≤ z.re ∧ 0 ≤ z.im - (j : ℝ) * H ∧
        z.im - (j : ℝ) * H ≤ H ∧ z.re + (z.im - (j : ℝ) * H) ≤
          (2 * m - (j : ℝ)) * H
      exact ⟨hz.1, by linarith [hz.2.1], by nlinarith [hz.2.2.1],
        by nlinarith [hz.2.2.2]⟩
    · apply Complex.ext <;> simp

theorem hexCoordinates_add (z w : ℂ) :
    hexCoordinates (z + w) = hexCoordinates z + hexCoordinates w := by
  simp only [hexCoordinates_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add]
  ring

theorem hexTrapezoidRow_translate (H : ℝ) (m : ℕ) (j : Fin m) :
    (IsometryEquiv.vaddConst (hexCoordinates (⟨0, (j : ℝ) * H⟩ : ℂ))) ''
      (hexCoordinates '' slantedTrapezoid H ((2 * m - (j : ℝ)) * H)) =
        hexCoordinates '' trapezoidRow H m j := by
  rw [← trapezoidRow_translate H m j, Set.image_image, Set.image_image]
  congr 1
  funext z
  change hexCoordinates z + hexCoordinates (⟨0, (j : ℝ) * H⟩ : ℂ) =
    hexCoordinates (z + (⟨0, (j : ℝ) * H⟩ : ℂ))
  exact (hexCoordinates_add _ _).symm

noncomputable def stackSlantedTrapezoidTilings (H : ℝ) (hH : 0 < H)
    (m : ℕ) (hm : 0 < m) {R : Triangle} {ι : Fin m → Type*}
    (T : ∀ j : Fin m, RegionTiling
      (hexCoordinates '' slantedTrapezoid H ((2 * m - (j : ℝ)) * H)) R (ι j)) :
    RegionTiling (hexCoordinates '' slantedTrapezoid ((m : ℝ) * H) (2 * m * H))
      R (Sigma ι) := by
  let U (j : Fin m) : RegionTiling (hexCoordinates '' trapezoidRow H m j) R (ι j) :=
    ((T j).mapIsometry (IsometryEquiv.vaddConst
      (hexCoordinates (⟨0, (j : ℝ) * H⟩ : ℂ)))).of_region_eq
        (hexTrapezoidRow_translate H m j)
  have hd : Pairwise fun i j : Fin m => Disjoint
      (interior (hexCoordinates '' trapezoidRow H m i))
      (interior (hexCoordinates '' trapezoidRow H m j)) := by
    intro i j hij
    exact disjoint_interiors_affine_image hexCoordinates (trapezoidRows_disjoint H hH m hij)
  apply (RegionTiling.indexedUnion U hd).of_region_eq
  rw [← Set.image_iUnion, trapezoidRows_cover H hH m hm]

end Erdos633
