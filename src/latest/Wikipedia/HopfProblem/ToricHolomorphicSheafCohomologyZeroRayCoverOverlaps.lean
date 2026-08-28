import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverLift
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultDoublePunctured

/-!
# Genuine coordinate biholomorphisms on all intersections of the zero-ray cover

The three pair intersections are actual punctured affine products. The
triple intersection is the actual double-punctured product. Each forward
map uses the actual inverse blowdown and each inverse uses its literal
projective coordinate, with the cyclic-coordinate swaps already proved.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

open ToricCharts ToricComponent

def firstDomain : Opens (ℂ × ℂ) :=
  ⟨{q | q.1 ≠ 0}, isOpen_ne_fun continuous_fst continuous_const⟩

abbrev secondDomain := OpenDolbeault.puncturedOpen
abbrev tripleDomain := OpenDolbeault.doublePuncturedOpen
abbrev pairOpen (i j : Fin 3) : Opens component := cover i ⊓ cover j
abbrev tripleOpen : Opens component := ThreeCover.tripleOpen (X := TopCat.of component) cover

@[simp] theorem mem_firstDomain (q : ℂ × ℂ) : q ∈ firstDomain ↔ q.1 ≠ 0 := Iff.rfl

theorem pair01_domain_punctured (q : ℂ × ℂ) (hq : q ∈ firstDomain) :
    standardProjectiveMap 0 q ∈ ProjectivePlane.puncturedSpace :=
  punctured_of_mem_two (i := 0) (j := 1) (by decide)
    (standardProjectiveMap_mem_self 0 q) ((standardProjectiveMap_mem_zero_one q).mpr hq)

theorem pair02_domain_punctured (q : ℂ × ℂ) (hq : q ∈ secondDomain) :
    standardProjectiveMap 0 q ∈ ProjectivePlane.puncturedSpace :=
  punctured_of_mem_two (i := 0) (j := 2) (by decide)
    (standardProjectiveMap_mem_self 0 q) ((standardProjectiveMap_mem_zero_two q).mpr hq)

theorem pair12_domain_punctured (q : ℂ × ℂ) (hq : q ∈ secondDomain) :
    standardProjectiveMap 1 q ∈ ProjectivePlane.puncturedSpace :=
  punctured_of_mem_two (i := 1) (j := 2) (by decide)
    (standardProjectiveMap_mem_self 1 q) ((standardProjectiveMap_mem_one_two q).mpr hq)

theorem triple_domain_punctured (q : ℂ × ℂ) (hq : q ∈ tripleDomain) :
    standardProjectiveMap 0 q ∈ ProjectivePlane.puncturedSpace :=
  pair01_domain_punctured q hq.1

theorem coordinates_zero_first_ne (x : component) (h0 : x ∈ cover 0) (h1 : x ∈ cover 1) :
    (coordinates 0 x).1 ≠ 0 := by
  apply (standardProjectiveMap_mem_zero_one _).mp
  rw [standardProjectiveMap_coordinates 0 x h0]
  exact (blowdown_mem_affineTarget_iff 1 x).mpr h1

theorem coordinates_zero_second_ne (x : component) (h0 : x ∈ cover 0) (h2 : x ∈ cover 2) :
    (coordinates 0 x).2 ≠ 0 := by
  apply (standardProjectiveMap_mem_zero_two _).mp
  rw [standardProjectiveMap_coordinates 0 x h0]
  exact (blowdown_mem_affineTarget_iff 2 x).mpr h2

theorem coordinates_one_second_ne (x : component) (h1 : x ∈ cover 1) (h2 : x ∈ cover 2) :
    (coordinates 1 x).2 ≠ 0 := by
  apply (standardProjectiveMap_mem_one_two _).mp
  rw [standardProjectiveMap_coordinates 1 x h1]
  exact (blowdown_mem_affineTarget_iff 2 x).mpr h2

/-- The actual `01` intersection in `[1:x:y]` coordinates, with `x ≠ 0`. -/
def pair01Biholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) firstDomain (pairOpen 0 1) ω :=
  coordinateBiholomorph 0 firstDomain pair01_domain_punctured (pairOpen 0 1) inf_le_left
    (fun q =>
      ⟨(liftMap_mem_cover_iff 0 firstDomain pair01_domain_punctured 0 q).mpr
          (standardProjectiveMap_mem_self 0 q),
        (liftMap_mem_cover_iff 0 firstDomain pair01_domain_punctured 1 q).mpr
          ((standardProjectiveMap_mem_zero_one q).mpr q.property)⟩)
    (fun x => coordinates_zero_first_ne x x.property.1 x.property.2)

/-- The actual `02` intersection in `[1:x:y]` coordinates, with `y ≠ 0`. -/
def pair02Biholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) secondDomain (pairOpen 0 2) ω :=
  coordinateBiholomorph 0 secondDomain pair02_domain_punctured (pairOpen 0 2) inf_le_left
    (fun q =>
      ⟨(liftMap_mem_cover_iff 0 secondDomain pair02_domain_punctured 0 q).mpr
          (standardProjectiveMap_mem_self 0 q),
        (liftMap_mem_cover_iff 0 secondDomain pair02_domain_punctured 2 q).mpr
          ((standardProjectiveMap_mem_zero_two q).mpr q.property)⟩)
    (fun x => coordinates_zero_second_ne x x.property.1 x.property.2)

/-- The actual `12` intersection in `[u:1:v]` coordinates, with `v ≠ 0`. -/
def pair12Biholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) secondDomain (pairOpen 1 2) ω :=
  coordinateBiholomorph 1 secondDomain pair12_domain_punctured (pairOpen 1 2) inf_le_left
    (fun q =>
      ⟨(liftMap_mem_cover_iff 1 secondDomain pair12_domain_punctured 1 q).mpr
          (standardProjectiveMap_mem_self 1 q),
        (liftMap_mem_cover_iff 1 secondDomain pair12_domain_punctured 2 q).mpr
          ((standardProjectiveMap_mem_one_two q).mpr q.property)⟩)
    (fun x => coordinates_one_second_ne x x.property.1 x.property.2)

/-- The literal triple intersection, with both coordinates nonzero. -/
def tripleBiholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) tripleDomain tripleOpen ω :=
  coordinateBiholomorph 0 tripleDomain triple_domain_punctured tripleOpen
    (inf_le_left.trans inf_le_left)
    (fun q =>
      ⟨⟨(liftMap_mem_cover_iff 0 tripleDomain triple_domain_punctured 0 q).mpr
            (standardProjectiveMap_mem_self 0 q),
          (liftMap_mem_cover_iff 0 tripleDomain triple_domain_punctured 1 q).mpr
            ((standardProjectiveMap_mem_zero_one q).mpr q.property.1)⟩,
        (liftMap_mem_cover_iff 0 tripleDomain triple_domain_punctured 2 q).mpr
          ((standardProjectiveMap_mem_zero_two q).mpr q.property.2)⟩)
    (fun x => ⟨coordinates_zero_first_ne x x.property.1.1 x.property.1.2,
      coordinates_zero_second_ne x x.property.1.1 x.property.2⟩)

@[simp] theorem pair01Biholomorph_symm_apply (x : pairOpen 0 1) :
    (pair01Biholomorph.symm x : ℂ × ℂ) = coordinates 0 x := rfl

@[simp] theorem pair02Biholomorph_symm_apply (x : pairOpen 0 2) :
    (pair02Biholomorph.symm x : ℂ × ℂ) = coordinates 0 x := rfl

@[simp] theorem pair12Biholomorph_symm_apply (x : pairOpen 1 2) :
    (pair12Biholomorph.symm x : ℂ × ℂ) = coordinates 1 x := rfl

@[simp] theorem tripleBiholomorph_symm_apply (x : tripleOpen) :
    (tripleBiholomorph.symm x : ℂ × ℂ) = coordinates 0 x := rfl

@[simp] theorem blowdown_pair01Biholomorph (q : firstDomain) :
    blowdown (pair01Biholomorph q) = standardProjectiveMap 0 q :=
  blowdown_liftMap 0 firstDomain pair01_domain_punctured q

@[simp] theorem blowdown_pair02Biholomorph (q : secondDomain) :
    blowdown (pair02Biholomorph q) = standardProjectiveMap 0 q :=
  blowdown_liftMap 0 secondDomain pair02_domain_punctured q

@[simp] theorem blowdown_pair12Biholomorph (q : secondDomain) :
    blowdown (pair12Biholomorph q) = standardProjectiveMap 1 q :=
  blowdown_liftMap 1 secondDomain pair12_domain_punctured q

@[simp] theorem blowdown_tripleBiholomorph (q : tripleDomain) :
    blowdown (tripleBiholomorph q) = standardProjectiveMap 0 q :=
  blowdown_liftMap 0 tripleDomain triple_domain_punctured q

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
