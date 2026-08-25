import StackExchange.Puzzling139335.ExteriorContact.ModelSpokes
import StackExchange.Puzzling139335.JordanAccessibility

/-!
# Access spokes in a Jordan exterior

Inversion exchanges a Jordan exterior with a punctured bounded Jordan domain.
The puncture is avoided explicitly by the three spokes constructed in a square
chart.  No boundedness assertion about the original exterior is used.
-/

open Set

namespace Schoenflies.IsJordanCurve

/-- Three boundary spokes can avoid an arbitrary prescribed interior point;
the common interior endpoint is chosen as part of the construction. -/
theorem exists_three_spokes_avoiding {C : Set Plane} {a : Plane}
    (hC : IsJordanCurve C) (ha : a ∈ inside C)
    (b : Fin 3 → Plane) (hb : ∀ i, b i ∈ C) (hinj : Function.Injective b) :
    ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∈ inside C ∧ x ≠ a ∧
      (∀ i, IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ inside C) ∧
      (∀ i, a ∉ A i) ∧ ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  obtain ⟨F, G, hF, hFC, hFin, hFa⟩ := hC.exists_pointed_square_chart ha
  have hbF (i : Fin 3) : F (b i) ∈ modelCurve := by
    rw [← hFC]
    exact ⟨b i, hb i, rfl⟩
  have hbinj : Function.Injective (F ∘ b) := by
    intro i j hij
    exact hinj (hF.injOn (Or.inl (hb i)) (Or.inl (hb j)) hij)
  obtain ⟨z, B, hz, hz0, hBarc, hBint, hBavoid, hBmeet⟩ :=
    exists_modelSquare_punctured_spokes (F ∘ b) hbF hbinj
  have hGFin : MapsTo G (Plane.openSquare 0 1) (inside C) := by
    intro w hw
    rw [← hFin] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    simpa only [hF.invOn.1 (Or.inr hv)] using hv
  have hBsub (i : Fin 3) : B i ⊆ Plane.closedSquare 0 1 := by
    intro w hw
    by_cases hwb : w = F (b i)
    · exact hwb ▸ modelCurve_subset_closedSquare (hbF i)
    · exact Plane.openSquare_subset_closedSquare 0 1 (hBint i ⟨hw, hwb⟩)
  have hGFb (i : Fin 3) : G (F (b i)) = b i := hF.invOn.1 (Or.inl (hb i))
  have hGza : G z ≠ a := by
    intro h
    apply hz0
    calc
      z = F (G z) := (hF.invOn.2 (Plane.openSquare_subset_closedSquare 0 1 hz)).symm
      _ = F a := congrArg F h
      _ = 0 := hFa
  refine ⟨G z, fun i => G '' B i, hGFin hz, hGza, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [Function.comp_apply, hGFb] using
      (hBarc i).image_of_injOn (hBsub i) hF.continuousOn_inv hF.symm.injOn
  · intro i w hw
    obtain ⟨⟨v, hv, rfl⟩, hwb⟩ := hw
    apply hGFin
    apply hBint i
    refine ⟨hv, ?_⟩
    intro hvb
    apply hwb
    change v = F (b i) at hvb
    exact mem_singleton_iff.mpr ((congrArg G hvb).trans (hGFb i))
  · intro i hai
    obtain ⟨v, hv, hva⟩ := hai
    have hv0 : v = 0 := by
      calc
        v = F (G v) := (hF.invOn.2 (hBsub i hv)).symm
        _ = F a := congrArg F hva
        _ = 0 := hFa
    exact hBavoid i (hv0 ▸ hv)
  · intro i j hij
    rw [← hF.symm.injOn.image_inter (hBsub i) (hBsub j), hBmeet i j hij,
      image_singleton]

/-- Any three distinct points on a Jordan curve admit disjoint access spokes
from one common point in its unbounded complementary region. -/
theorem exists_three_exterior_spokes {C : Set Plane} (hC : IsJordanCurve C)
    (b : Fin 3 → Plane) (hb : ∀ i, b i ∈ C) (hinj : Function.Injective b) :
    ∃ x : Plane, ∃ A : Fin 3 → Set Plane,
      x ∈ outside C ∧
      (∀ i, IsArcBetween (A i) x (b i)) ∧
      (∀ i, A i \ {b i} ⊆ outside C) ∧
      ∀ i j, i ≠ j → A i ∩ A j = {x} := by
  obtain ⟨a, ha⟩ := (jordan_curve_theorem hC).isConnected_inside.nonempty
  have hCi : IsJordanCurve (invert a '' C) := hC.invert_image ha.1
  have hai : a ∈ inside (invert a '' C) :=
    mem_inside_invert_image (fun _ hA => arc_complement hA) hC ha
  have hbi (i : Fin 3) : invert a (b i) ∈ invert a '' C := ⟨b i, hb i, rfl⟩
  have hinji : Function.Injective (invert a ∘ b) := (invert_injective a).comp hinj
  obtain ⟨y, B, hy, hya, hBarc, hBint, hBavoid, hBmeet⟩ :=
    hCi.exists_three_spokes_avoiding hai (invert a ∘ b) hbi hinji
  have hIout : invert a '' outside C = inside (invert a '' C) \ {a} :=
    invert_image_outside (fun _ hA => arc_complement hA) hC ha
  have hInvOut : MapsTo (invert a) (inside (invert a '' C) \ {a}) (outside C) := by
    intro z hz
    rw [← hIout] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [invert_invert] using hw
  have hBsub (i : Fin 3) : B i ⊆ ({a}ᶜ : Set Plane) := by
    intro z hz hza
    exact hBavoid i (mem_singleton_iff.mp hza ▸ hz)
  refine ⟨invert a y, fun i => invert a '' B i, hInvOut ⟨hy, hya⟩, ?_, ?_, ?_⟩
  · intro i
    simpa only [Function.comp_apply, invert_invert] using
      (hBarc i).image_of_injOn (hBsub i) (continuousOn_invert a) (invert_injective a).injOn
  · intro i z hz
    obtain ⟨⟨w, hw, rfl⟩, hzb⟩ := hz
    apply hInvOut
    refine ⟨hBint i ⟨hw, ?_⟩, hBsub i hw⟩
    intro hwb
    apply hzb
    change w = invert a (b i) at hwb
    exact mem_singleton_iff.mpr ((congrArg (invert a) hwb).trans (invert_invert a (b i)))
  · intro i j hij
    rw [← image_inter (invert_injective a), hBmeet i j hij, image_singleton]

end Schoenflies.IsJordanCurve
