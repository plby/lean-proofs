import Wikipedia.NoExoticSixSphere.JamesSphereConeCorrection
import Wikipedia.NoExoticSixSphere.CellChartSmoothingInput
import Wikipedia.NoExoticSixSphere.OpenMapHomotopyExtension

/-!
# Extending the cone-face correction by a constructed support cutoff

A closed source subset whose image misses the first cell point can be
pushed into the cone disk. The actual global homotopy fixes cone points,
preserves the James-stage image, and never creates a hit of the second
chosen point. The cutoff and the extension are constructed on the
original normal source space; no boundary extension data are assumed.
-/

noncomputable section

open Set Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

theorem range_firstCell (n : ℕ) (hn : 0 < n) : Set.range (firstCell n) = Set.range (base n) := by
  apply Set.Subset.antisymm
  · rintro z ⟨d, rfl⟩
    exact Set.mem_range_self (Cell.closedPresentation n 2 d)
  · rintro z ⟨w, rfl⟩
    obtain ⟨d, hd⟩ := Cell.closedPresentation_surjective n 2 hn w
    exact ⟨d, congrArg (base n) hd⟩

theorem firstDeformation_mem_base (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
    (t : I) (x : firstPunctured n p hp) (hx : x.val ∈ Set.range (base n)) :
    (firstPunctureDeformation n hn p hp (t, x)).val ∈ Set.range (base n) := by
  have hx' : x.val ∈ Set.range (firstCell n) := by rwa [range_firstCell n hn]
  have h := PuncturedCellAttachment.deformation_cell_mem (first_isPushout n hn) p hp t x hx'
  change (firstPunctureDeformation n hn p hp (t, x)).val ∈ Set.range (firstCell n) at h
  rwa [range_firstCell n hn] at h

namespace SupportedCorrection

variable (n : ℕ) (hn : 0 < n) (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
  {D : Type} [TopologicalSpace D] (f : C(D, Space n))

abbrev Domain := f ⁻¹' (firstPunctured n p hp : Set (Space n))

def localInput : C(Domain n p hp f, firstPunctured n p hp) :=
  ⟨fun x ↦ ⟨f x.val, x.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

def localFamily : C(I × Domain n p hp f, Space n) :=
  ⟨fun z ↦ (firstPunctureDeformation n hn p hp (z.1, localInput n p hp f z.2)).val,
    continuous_subtype_val.comp ((firstPunctureDeformation n hn p hp).continuous.comp
      (continuous_fst.prodMk ((localInput n p hp f).continuous.comp continuous_snd)))⟩

theorem localFamily_zero (x : Domain n p hp f) : localFamily n hn p hp f (0, x) = f x.val :=
  congrArg (fun y : firstPunctured n p hp ↦ y.val)
    ((firstPunctureDeformation n hn p hp).map_zero_left (localInput n p hp f x))

theorem localFamily_one_mem_cone (x : Domain n p hp f) :
    localFamily n hn p hp f (1, x) ∈ Set.range (cone n) :=
  ⟨firstPunctureRetraction n hn p hp (localInput n p hp f x),
    (congrArg (fun y : firstPunctured n p hp ↦ y.val)
      ((firstPunctureDeformation n hn p hp).map_one_left (localInput n p hp f x))).symm⟩

theorem localFamily_fixed (t : I) (x : Domain n p hp f)
    (hx : f x.val ∈ Set.range (cone n)) : localFamily n hn p hp f (t, x) = f x.val :=
  congrArg (fun y : firstPunctured n p hp ↦ y.val)
    (PuncturedCellAttachment.deformation_fixed_of_mem_base (first_isPushout n hn) p hp t
      (localInput n p hp f x) hx)

theorem localFamily_mem_base (t : I) (x : Domain n p hp f)
    (hx : f x.val ∈ Set.range (base n)) : localFamily n hn p hp f (t, x) ∈ Set.range (base n) :=
  firstDeformation_mem_base n hn p hp t (localInput n p hp f x) hx

theorem localFamily_avoids (q : ConeCoordinates n) (hq : ‖q‖ < 1) (t : I)
    (x : Domain n p hp f) (hx : f x.val ≠ cone n (PuncturedCellAttachment.point q hq)) :
    localFamily n hn p hp f (t, x) ≠ cone n (PuncturedCellAttachment.point q hq) :=
  PuncturedCellAttachment.deformation_avoids_of_not_mem_cell (first_isPushout n hn) p hp
    (cone n (PuncturedCellAttachment.point q hq)) (secondPoint_not_firstCell n q hq)
    t (localInput n p hp f x) hx

variable [NormalSpace D]

include hn in
theorem exists_correction (q : ConeCoordinates n) (hq : ‖q‖ < 1)
    (K : Set D) (hK : IsClosed K) (havoid : K ⊆ Domain n p hp f) :
    ∃ g : C(D, Space n), ∃ H : f.Homotopy g,
      (∀ t z, f z ∈ Set.range (cone n) → H (t, z) = f z) ∧
      (∀ t z, f z ∈ Set.range (base n) → H (t, z) ∈ Set.range (base n)) ∧
      (∀ t z, f z ≠ cone n (PuncturedCellAttachment.point q hq) →
        H (t, z) ≠ cone n (PuncturedCellAttachment.point q hq)) ∧
      ∀ z ∈ K, g z ∈ Set.range (cone n) := by
  have hU : IsOpen (Domain n p hp f) := (firstPunctured n p hp).isOpen.preimage f.continuous
  obtain ⟨β, hβK, hsupp, hβ⟩ := CellChart.exists_supported_cutoff K (Domain n p hp f) hK hU havoid
  let L := localFamily n hn p hp f
  have hzero : ∀ x, L (0, x) = f x.val := localFamily_zero n hn p hp f
  let g := OpenMapHomotopyExtension.endpoint f L β hβ hzero hU hsupp
  let H := OpenMapHomotopyExtension.homotopy f L β hβ hzero hU hsupp
  refine ⟨g, H, ?_, ?_, ?_, ?_⟩
  · intro t z hz
    change OpenMapHomotopyExtension.raw f L β hβ (t, z) = f z
    by_cases hzu : z ∈ Domain n p hp f
    · rw [OpenMapHomotopyExtension.raw_of_mem f L β hβ hzu]
      exact localFamily_fixed n hn p hp f _ ⟨z, hzu⟩ hz
    · exact OpenMapHomotopyExtension.raw_of_notMem f L β hβ hzu t
  · intro t z hz
    change OpenMapHomotopyExtension.raw f L β hβ (t, z) ∈ Set.range (base n)
    by_cases hzu : z ∈ Domain n p hp f
    · rw [OpenMapHomotopyExtension.raw_of_mem f L β hβ hzu]
      exact localFamily_mem_base n hn p hp f _ ⟨z, hzu⟩ hz
    · rwa [OpenMapHomotopyExtension.raw_of_notMem f L β hβ hzu]
  · intro t z hz
    change OpenMapHomotopyExtension.raw f L β hβ (t, z) ≠
      cone n (PuncturedCellAttachment.point q hq)
    by_cases hzu : z ∈ Domain n p hp f
    · rw [OpenMapHomotopyExtension.raw_of_mem f L β hβ hzu]
      exact localFamily_avoids n hn p hp f q hq _ ⟨z, hzu⟩ hz
    · rwa [OpenMapHomotopyExtension.raw_of_notMem f L β hβ hzu]
  · intro z hz
    change OpenMapHomotopyExtension.endpoint f L β hβ hzero hU hsupp z ∈ Set.range (cone n)
    rw [OpenMapHomotopyExtension.endpoint_of_one f L β hβ hzero hU hsupp (havoid hz) (hβK hz)]
    exact localFamily_one_mem_cone n hn p hp f ⟨z, havoid hz⟩

end SupportedCorrection

end NoExoticSixSphere.JamesSphere.SecondStageCone
