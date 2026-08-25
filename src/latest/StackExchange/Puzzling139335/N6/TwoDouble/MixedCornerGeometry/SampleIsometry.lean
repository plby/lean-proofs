import StackExchange.Puzzling139335.N6.TwoDouble.MixedScalar
import StackExchange.Puzzling139335.SquareSymmetry.SideRigidity.Normalized

/-!
# Relative isometries determined by two actual side samples

Suppose an affine isometry takes the bottom-right corner to the top-right
corner. The source and target each contain a positive sample on the right
side, directed into that side from the corresponding corner. If both sets
fit in the square and the source has nonempty interior, the isometry either
fixes the center or is one of the strict oblique rotations used in the mixed
six-incidence obstruction. No boundary-germ or hull-ray hypothesis is used.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.MixedCornerGeometry.SampleIsometry

noncomputable section

open PlaneIsometries

private theorem direct_corner_coordinates (g : Plane ≃ᵃⁱ[ℝ] Plane)
    {k l : ℝ} (hbase : g (corner 1) = corner 2)
    (hform : ∀ p, g p = directCoordinates k l (g 0) p) (p : Plane) :
    g p 0 = 1 + k * (p 0 - 1) - l * p 1 ∧
      g p 1 = 1 + l * (p 0 - 1) + k * p 1 := by
  have hb := hform (corner 1)
  rw [hbase] at hb
  have hb0 := congrArg (fun q : Plane => q 0) hb
  have hb1 := congrArg (fun q : Plane => q 1) hb
  norm_num [directCoordinates, corner, Fin.ext_iff] at hb0 hb1
  have hp0 := congrArg (fun q : Plane => q 0) (hform p)
  have hp1 := congrArg (fun q : Plane => q 1) (hform p)
  change g p 0 = k * p 0 - l * p 1 + g 0 0 at hp0
  change g p 1 = l * p 0 + k * p 1 + g 0 1 at hp1
  constructor
  · nlinarith only [hb0, hp0]
  · nlinarith only [hb1, hp1]

private theorem reversing_corner_coordinates (g : Plane ≃ᵃⁱ[ℝ] Plane)
    {k l : ℝ} (hbase : g (corner 1) = corner 2)
    (hform : ∀ p, g p = reversingCoordinates k l (g 0) p) (p : Plane) :
    g p 0 = 1 + k * (p 0 - 1) + l * p 1 ∧
      g p 1 = 1 + l * (p 0 - 1) - k * p 1 := by
  have hb := hform (corner 1)
  rw [hbase] at hb
  have hb0 := congrArg (fun q : Plane => q 0) hb
  have hb1 := congrArg (fun q : Plane => q 1) hb
  norm_num [reversingCoordinates, corner, Fin.ext_iff] at hb0 hb1
  have hp0 := congrArg (fun q : Plane => q 0) (hform p)
  have hp1 := congrArg (fun q : Plane => q 1) (hform p)
  change g p 0 = k * p 0 + l * p 1 + g 0 0 at hp0
  change g p 1 = l * p 0 - k * p 1 + g 0 1 at hp1
  constructor
  · nlinarith only [hb0, hp0]
  · nlinarith only [hb1, hp1]

private theorem direct_sample_signs {k l t : ℝ} (ht : 0 < t)
    {g : Plane → Plane}
    (hcoord : ∀ p, g p 0 = 1 + k * (p 0 - 1) - l * p 1 ∧
      g p 1 = 1 + l * (p 0 - 1) + k * p 1)
    (hfit : g (!₂[(1 : ℝ), t]) ∈ unitSquare) : k ≤ 0 ∧ 0 ≤ l := by
  obtain ⟨h0, h1⟩ := hcoord (!₂[(1 : ℝ), t])
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_self, mul_zero, add_zero] at h0 h1
  have hkt : k * t ≤ 0 := by linarith only [hfit.2.2, h1]
  have hlt : 0 ≤ l * t := by linarith only [hfit.1.2, h0]
  exact ⟨nonpos_of_mul_nonpos_left hkt ht,
    (mul_nonneg_iff_of_pos_right ht).mp hlt⟩

private theorem direct_classification {H : Set Plane}
    (hH : H ⊆ unitSquare) (hint : (interior H).Nonempty)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (hfit : g '' H ⊆ unitSquare)
    {k l : ℝ} (hcircle : k ^ 2 + l ^ 2 = 1)
    (hcoord : ∀ p, g p 0 = 1 + k * (p 0 - 1) - l * p 1 ∧
      g p 1 = 1 + l * (p 0 - 1) + k * p 1)
    {t : ℝ} (ht : 0 < t) (hsample : !₂[(1 : ℝ), t] ∈ H) :
    g squareCenter = squareCenter ∨
      ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s ^ 2 + c ^ 2 = 1 ∧
        ∀ p, g p = MixedScalar.rotation s c p := by
  obtain ⟨hk, hl⟩ := direct_sample_signs ht hcoord
    (hfit (mem_image_of_mem g hsample))
  by_cases hkzero : k = 0
  · have hlone : l = 1 := by nlinarith only [hcircle, hkzero, hl]
    left
    apply plane_ext
    · have h := (hcoord squareCenter).1
      norm_num [squareCenter, hkzero, hlone] at h
      exact h
    · have h := (hcoord squareCenter).2
      norm_num [squareCenter, hkzero, hlone] at h
      exact h
  · have hlne : l ≠ 0 := by
      intro hlzero
      have hkneg : k = -1 := by nlinarith only [hcircle, hlzero, hk]
      obtain ⟨p, hp⟩ := hint
      have hpcoord := SquareSymmetry.interior_unitSquare_coordinates (interior_mono hH hp)
      have hgfit := hfit (mem_image_of_mem g (interior_subset hp))
      have hgp := (hcoord p).1
      rw [hkneg, hlzero] at hgp
      nlinarith only [hpcoord.1.2, hgfit.1.2, hgp]
    right
    refine ⟨-k, l, ?_, lt_of_le_of_ne hl (Ne.symm hlne), ?_, ?_⟩
    · exact neg_pos.mpr (lt_of_le_of_ne hk hkzero)
    · nlinarith only [hcircle]
    · intro p
      apply plane_ext
      · change g p 0 = 1 + -k - -k * p 0 - l * p 1
        nlinarith only [(hcoord p).1]
      · change g p 1 = 1 - l + l * p 0 - -k * p 1
        nlinarith only [(hcoord p).2]

private theorem reversing_classification {H G : Set Plane}
    (hH : H ⊆ unitSquare) (hG : G ⊆ unitSquare)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (himage : g '' H = G)
    {k l : ℝ} (hcircle : k ^ 2 + l ^ 2 = 1)
    (hcoord : ∀ p, g p 0 = 1 + k * (p 0 - 1) + l * p 1 ∧
      g p 1 = 1 + l * (p 0 - 1) - k * p 1)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hsample : !₂[(1 : ℝ), t] ∈ H)
    (htarget : !₂[(1 : ℝ), 1 - u] ∈ G) :
    g squareCenter = squareCenter := by
  have hsamplefit : g (!₂[(1 : ℝ), t]) ∈ unitSquare := by
    apply hG
    rw [← himage]
    exact mem_image_of_mem g hsample
  obtain ⟨h0, h1⟩ := hcoord (!₂[(1 : ℝ), t])
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sub_self, mul_zero, add_zero] at h0 h1
  have hkt : 0 ≤ k * t := by linarith only [hsamplefit.2.2, h1]
  have hlt : l * t ≤ 0 := by linarith only [hsamplefit.1.2, h0]
  have hk : 0 ≤ k := (mul_nonneg_iff_of_pos_right ht).mp hkt
  have hl : l ≤ 0 := nonpos_of_mul_nonpos_left hlt ht
  rw [← himage] at htarget
  obtain ⟨p, hp, hgp⟩ := htarget
  obtain ⟨hp0, hp1⟩ := hcoord p
  rw [hgp] at hp0 hp1
  change 1 = 1 + k * (p 0 - 1) + l * p 1 at hp0
  change 1 - u = 1 + l * (p 0 - 1) - k * p 1 at hp1
  have hx : p 0 - 1 = -(l * u) := by
    calc
      p 0 - 1 = (k ^ 2 + l ^ 2) * (p 0 - 1) := by rw [hcircle, one_mul]
      _ = k * (k * (p 0 - 1) + l * p 1) +
          l * (l * (p 0 - 1) - k * p 1) := by ring
      _ = -(l * u) := by
        have hzero : k * (p 0 - 1) + l * p 1 = 0 := by linarith only [hp0]
        have hdown : l * (p 0 - 1) - k * p 1 = -u := by linarith only [hp1]
        rw [hzero, hdown]
        ring
  have hlmul : 0 ≤ l * u := by linarith only [hx, (hH hp).1.2]
  have hlzero : l = 0 := le_antisymm hl ((mul_nonneg_iff_of_pos_right hu).mp hlmul)
  have hkone : k = 1 := by nlinarith only [hcircle, hlzero, hk]
  apply plane_ext
  · have h := (hcoord squareCenter).1
    norm_num [squareCenter, hkone, hlzero] at h
    exact h
  · have h := (hcoord squareCenter).2
    norm_num [squareCenter, hkone, hlzero] at h
    exact h

/-- Two independently supplied actual side samples restrict every fitting
relative isometry to a center-fixing motion or the strict oblique rotation.
The two samples are not assumed to be images of one another. -/
theorem classification_of_side_samples {H G : Set Plane}
    (hH : H ⊆ unitSquare) (hG : G ⊆ unitSquare)
    (hint : (interior H).Nonempty)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (himage : g '' H = G)
    (hbase : g (corner 1) = corner 2)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hsample : !₂[(1 : ℝ), t] ∈ H)
    (htarget : !₂[(1 : ℝ), 1 - u] ∈ G) :
    g squareCenter = squareCenter ∨
      ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s ^ 2 + c ^ 2 = 1 ∧
        ∀ p, g p = MixedScalar.rotation s c p := by
  obtain ⟨k, l, hcircle, hform | hform⟩ := affine_coordinate_classification g
  · have hfit : g '' H ⊆ unitSquare := by rwa [himage]
    exact direct_classification hH hint g hfit hcircle
      (direct_corner_coordinates g hbase hform) ht hsample
  · left
    exact reversing_classification hH hG g himage hcircle
      (reversing_corner_coordinates g hbase hform) ht hu hsample htarget

/-- The rotation alternative also gives equality of the actual image set. -/
theorem classification_of_side_samples_image {H G : Set Plane}
    (hH : H ⊆ unitSquare) (hG : G ⊆ unitSquare)
    (hint : (interior H).Nonempty)
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (himage : g '' H = G)
    (hbase : g (corner 1) = corner 2)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (hsample : !₂[(1 : ℝ), t] ∈ H)
    (htarget : !₂[(1 : ℝ), 1 - u] ∈ G) :
    g squareCenter = squareCenter ∨
      ∃ s c : ℝ, 0 < s ∧ 0 < c ∧ s ^ 2 + c ^ 2 = 1 ∧
        (∀ p, g p = MixedScalar.rotation s c p) ∧
        G = MixedScalar.rotation s c '' H := by
  rcases classification_of_side_samples hH hG hint g himage hbase ht hu hsample htarget
    with hcenter | ⟨s, c, hs, hc, hcircle, hform⟩
  · exact Or.inl hcenter
  · right
    refine ⟨s, c, hs, hc, hcircle, hform, ?_⟩
    rw [← himage]
    congr 1
    exact funext hform

end

end Puzzling139335.N6.TwoDouble.MixedCornerGeometry.SampleIsometry
