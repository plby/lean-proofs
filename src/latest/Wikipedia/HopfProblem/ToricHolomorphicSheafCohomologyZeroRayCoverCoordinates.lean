import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyZeroRayCoverBasic

/-!
# Literal projective coordinates for the zero-ray three-open cover

The analytic solvers use pairs `(x,y)`, `(u,v)`, and `(s,t)` for the actual
homogeneous coordinates `[1:x:y]`, `[u:1:v]`, and `[t:s:1]`. Thus the last
two pairs are swapped before entering the native cyclic projective charts.
All coordinate maps below are genuine holomorphic maps tied to blowdown.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover

open ToricCharts ToricComponent

/-- The exact complex-linear conversion to the cyclic native chart convention. -/
def standardLinearEquiv (k : Fin 3) : (ℂ × ℂ) ≃L[ℂ] CoordinateSpace 2 :=
  if k = 0 then Charts.productNativeLinearEquiv
  else (ContinuousLinearEquiv.prodComm ℂ ℂ ℂ).trans Charts.productNativeLinearEquiv

@[simp] theorem standardLinearEquiv_zero (q : ℂ × ℂ) :
    standardLinearEquiv 0 q = ![q.1, q.2] := rfl

@[simp] theorem standardLinearEquiv_one (q : ℂ × ℂ) :
    standardLinearEquiv 1 q = ![q.2, q.1] := rfl

@[simp] theorem standardLinearEquiv_two (q : ℂ × ℂ) :
    standardLinearEquiv 2 q = ![q.2, q.1] := rfl

def standardProjectiveMap (k : Fin 3) (q : ℂ × ℂ) : ProjectivePlane.Space :=
  ProjectivePlane.affineMap k (standardLinearEquiv k q)

def standardProjectiveCoords (k : Fin 3) (x : ProjectivePlane.Space) : ℂ × ℂ :=
  (standardLinearEquiv k).symm (ProjectivePlane.affineCoords k x)

@[simp] theorem standardProjectiveCoords_map (k : Fin 3) (q : ℂ × ℂ) :
    standardProjectiveCoords k (standardProjectiveMap k q) = q := by
  simp only [standardProjectiveCoords, standardProjectiveMap,
    ProjectivePlane.affineCoords_affineMap, ContinuousLinearEquiv.symm_apply_apply]

theorem standardProjectiveMap_coords (k : Fin 3) (x : ProjectivePlane.Space)
    (hx : x ∈ ProjectivePlane.affineTarget k) :
    standardProjectiveMap k (standardProjectiveCoords k x) = x := by
  simp only [standardProjectiveCoords, standardProjectiveMap,
    ContinuousLinearEquiv.apply_symm_apply, ProjectivePlane.affineMap_affineCoords k x hx]

theorem standardProjectiveMap_holomorphic (k : Fin 3) :
    ContMDiff 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) ω (standardProjectiveMap k) :=
  (ProjectivePlane.affineMap_holomorphic k).comp (standardLinearEquiv k).contDiff.contMDiff

theorem standardProjectiveCoords_holomorphicOn (k : Fin 3) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ × ℂ) ω (standardProjectiveCoords k)
      (ProjectivePlane.affineTarget k) :=
  (standardLinearEquiv k).symm.contDiff.contMDiff.comp_contMDiffOn
    (ProjectivePlane.affineCoords_holomorphicOn k)

theorem standardProjectiveMap_mem_self (k : Fin 3) (q : ℂ × ℂ) :
    standardProjectiveMap k q ∈ ProjectivePlane.affineTarget k :=
  ProjectivePlane.affineMap_mem_target k _

@[simp] theorem standardProjectiveMap_mem_zero_one (q : ℂ × ℂ) :
    standardProjectiveMap 0 q ∈ ProjectivePlane.affineTarget 1 ↔ q.1 ≠ 0 :=
  ProjectivePlane.quotientMap_mem_affineTarget_iff 1 _

@[simp] theorem standardProjectiveMap_mem_zero_two (q : ℂ × ℂ) :
    standardProjectiveMap 0 q ∈ ProjectivePlane.affineTarget 2 ↔ q.2 ≠ 0 :=
  ProjectivePlane.quotientMap_mem_affineTarget_iff 2 _

@[simp] theorem standardProjectiveMap_mem_one_two (q : ℂ × ℂ) :
    standardProjectiveMap 1 q ∈ ProjectivePlane.affineTarget 2 ↔ q.2 ≠ 0 :=
  ProjectivePlane.quotientMap_mem_affineTarget_iff 2 _

theorem standardProjectiveCoords_zero_one (q : ℂ × ℂ) :
    standardProjectiveCoords 1 (standardProjectiveMap 0 q) = (q.1⁻¹, q.2 / q.1) := by
  change (1 / q.1, q.2 / q.1) = _
  simp only [one_div]

theorem standardProjectiveCoords_zero_two (q : ℂ × ℂ) :
    standardProjectiveCoords 2 (standardProjectiveMap 0 q) = (q.1 / q.2, q.2⁻¹) := by
  change (q.1 / q.2, 1 / q.2) = _
  simp only [one_div]

theorem standardProjectiveCoords_one_two (q : ℂ × ℂ) :
    standardProjectiveCoords 2 (standardProjectiveMap 1 q) = (q.2⁻¹, q.1 / q.2) := by
  change (1 / q.2, q.1 / q.2) = _
  simp only [one_div]

theorem standardProjectiveMap_zero_one (q : ℂ × ℂ) (hq : q.1 ≠ 0) :
    standardProjectiveMap 1 (q.1⁻¹, q.2 / q.1) = standardProjectiveMap 0 q := by
  rw [← standardProjectiveCoords_zero_one]
  exact standardProjectiveMap_coords 1 _ ((standardProjectiveMap_mem_zero_one q).mpr hq)

theorem standardProjectiveMap_zero_two (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    standardProjectiveMap 2 (q.1 / q.2, q.2⁻¹) = standardProjectiveMap 0 q := by
  rw [← standardProjectiveCoords_zero_two]
  exact standardProjectiveMap_coords 2 _ ((standardProjectiveMap_mem_zero_two q).mpr hq)

theorem standardProjectiveMap_one_two (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    standardProjectiveMap 2 (q.2⁻¹, q.1 / q.2) = standardProjectiveMap 1 q := by
  rw [← standardProjectiveCoords_one_two]
  exact standardProjectiveMap_coords 2 _ ((standardProjectiveMap_mem_one_two q).mpr hq)

/-- A projective point in two distinct affine charts is not a blowup center. -/
theorem punctured_of_mem_two {i j : Fin 3} (hij : i ≠ j) {p : ProjectivePlane.Space}
    (hi : p ∈ ProjectivePlane.affineTarget i) (hj : p ∈ ProjectivePlane.affineTarget j) :
    p ∈ ProjectivePlane.puncturedSpace := by
  rintro ⟨k, rfl⟩
  exact hij (((ProjectivePlane.coordinatePoint_mem_target_iff k i).mp hi).symm.trans
    ((ProjectivePlane.coordinatePoint_mem_target_iff k j).mp hj))

/-- The genuine ambient coordinates induced by the actual blowdown. -/
def coordinates (k : Fin 3) (x : component) : ℂ × ℂ :=
  standardProjectiveCoords k (blowdown x)

theorem coordinates_holomorphicOn (k : Fin 3) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ, ℂ × ℂ) ω (coordinates k) (cover k) :=
  (standardProjectiveCoords_holomorphicOn k).comp blowdown_holomorphic.contMDiffOn
    (fun x hx => (blowdown_mem_affineTarget_iff k x).mpr hx)

theorem standardProjectiveMap_coordinates (k : Fin 3) (x : component) (hx : x ∈ cover k) :
    standardProjectiveMap k (coordinates k x) = blowdown x :=
  standardProjectiveMap_coords k _ ((blowdown_mem_affineTarget_iff k x).mpr hx)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.ZeroRayCover
