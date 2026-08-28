import Wikipedia.HopfProblem.RiemannSphere
import Wikipedia.HopfProblem.ToricCharts

/-!
# The incidence model of the blow-up of the affine plane

The point `z` of the Riemann sphere represents the line `[z : 1]`, and
infinity represents `[1 : 0]`. The blow-up consists of pairs `(v, l)` with
`v` on the line `l`, with the actual subspace topology in `ℂ² × ℙ¹`.
The two affine parametrizations are `(u,v) ↦ ((uv,v),[u:1])` and
`(u,v) ↦ ((u,uv),[1:v])`.
-/

noncomputable section

open Set Topology OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.AffineBlowup

open ToricCharts

def Incidence (v : CoordinateSpace 2) (l : RiemannSphere) : Prop :=
  l.elim (v 1 = 0) (fun z : ℂ => v 0 = z * v 1)

@[simp] theorem incidence_coe (v : CoordinateSpace 2) (z : ℂ) :
    Incidence v (z : RiemannSphere) ↔ v 0 = z * v 1 := Iff.rfl

@[simp] theorem incidence_infty (v : CoordinateSpace 2) :
    Incidence v (∞ : RiemannSphere) ↔ v 1 = 0 := Iff.rfl

theorem incidence_infinityParametrization (v : CoordinateSpace 2) (z : ℂ) :
    Incidence v (RiemannSphere.infinityParametrization z) ↔ v 1 = z * v 0 := by
  by_cases hz : z = 0
  · subst z
    simp
  · rw [RiemannSphere.infinityParametrization_of_ne hz, incidence_coe]
    constructor
    · intro h
      rw [h, mul_inv_cancel_left₀ hz]
    · intro h
      rw [h, inv_mul_cancel_left₀ hz]

def incidenceSet : Set (CoordinateSpace 2 × RiemannSphere) := {p | Incidence p.1 p.2}

abbrev Space := incidenceSet

def projection (x : Space) : CoordinateSpace 2 := x.1.1

def direction (x : Space) : RiemannSphere := x.1.2

theorem continuous_projection : Continuous projection := continuous_fst.comp continuous_subtype_val

theorem continuous_direction : Continuous direction := continuous_snd.comp continuous_subtype_val

theorem incidence_point (x : Space) : Incidence (projection x) (direction x) := x.2

def left (z : CoordinateSpace 2) : Space :=
  ⟨(![z 0 * z 1, z 1], (z 0 : RiemannSphere)), rfl⟩

def right (z : CoordinateSpace 2) : Space :=
  ⟨(![z 0, z 0 * z 1], RiemannSphere.infinityParametrization (z 1)),
    (incidence_infinityParametrization _ _).mpr (mul_comm _ _)⟩

def affineMap (b : Bool) : CoordinateSpace 2 → Space := if b then right else left

theorem affineMap_continuous (b : Bool) : Continuous (affineMap b) := by
  cases b
  · change Continuous left
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous (fun z : CoordinateSpace 2 => ![z 0 * z 1, z 1])).prodMk
      (OnePoint.continuous_coe.comp (continuous_apply 0))
  · change Continuous right
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous (fun z : CoordinateSpace 2 => ![z 0, z 0 * z 1])).prodMk
      (RiemannSphere.infinityParametrization_continuous.comp (continuous_apply 1))

def affineTarget (b : Bool) : Set Space :=
  direction ⁻¹' range (RiemannSphere.standardCharts.affineMap b)

theorem affineTarget_isOpen (b : Bool) : IsOpen (affineTarget b) :=
  (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).isOpen_range.preimage
    continuous_direction

theorem affineMap_mem_target (b : Bool) (z : CoordinateSpace 2) :
    affineMap b z ∈ affineTarget b := by
  cases b
  · exact ⟨z 0, rfl⟩
  · exact ⟨z 1, rfl⟩

def affineCoords (b : Bool) (x : Space) : CoordinateSpace 2 :=
  if b then ![projection x 0,
    (RiemannSphere.standardCharts.parametrization true).symm (direction x)]
  else ![(RiemannSphere.standardCharts.parametrization false).symm (direction x), projection x 1]

theorem affineCoords_affineMap (b : Bool) (z : CoordinateSpace 2) :
    affineCoords b (affineMap b z) = z := by
  cases b
  · change ![(RiemannSphere.standardCharts.parametrization false).symm
      (RiemannSphere.standardCharts.affineMap false (z 0)), z 1] = z
    rw [TwoAffineCharts.parametrization_symm_apply]
    ext j
    fin_cases j <;> rfl
  · change ![z 0, (RiemannSphere.standardCharts.parametrization true).symm
      (RiemannSphere.standardCharts.affineMap true (z 1))] = z
    rw [TwoAffineCharts.parametrization_symm_apply]
    ext j
    fin_cases j <;> rfl

theorem affineMap_affineCoords (b : Bool) (x : Space) (hx : x ∈ affineTarget b) :
    affineMap b (affineCoords b x) = x := by
  obtain ⟨u, hu⟩ := hx
  have hc : (RiemannSphere.standardCharts.parametrization b).symm (direction x) = u := by
    rw [← hu, TwoAffineCharts.parametrization_symm_apply]
  have hi := incidence_point x
  rw [← hu] at hi
  cases b
  · change projection x 0 = u * projection x 1 at hi
    change left ![(RiemannSphere.standardCharts.parametrization false).symm (direction x),
      projection x 1] = x
    rw [hc]
    apply Subtype.ext
    apply Prod.ext
    · ext j
      fin_cases j
      · exact hi.symm
      · rfl
    · exact hu
  · have hi' : projection x 1 = u * projection x 0 :=
      (incidence_infinityParametrization _ _).mp hi
    change right ![projection x 0,
      (RiemannSphere.standardCharts.parametrization true).symm (direction x)] = x
    rw [hc]
    apply Subtype.ext
    apply Prod.ext
    · ext j
      fin_cases j
      · rfl
      · exact (mul_comm _ _).trans hi'.symm
    · exact hu

theorem affineCoords_continuousOn (b : Bool) : ContinuousOn (affineCoords b) (affineTarget b) := by
  have hd : ContinuousOn
      (fun x : Space => (RiemannSphere.standardCharts.parametrization b).symm (direction x))
      (affineTarget b) :=
    (RiemannSphere.standardCharts.parametrization b).symm.continuousOn.comp
      continuous_direction.continuousOn (by
        intro x hx
        change direction x ∈ (RiemannSphere.standardCharts.parametrization b).target
        rw [TwoAffineCharts.parametrization_target]
        exact hx)
  apply continuousOn_pi.mpr
  intro j
  cases b <;> fin_cases j
  · exact hd
  · exact ((continuous_apply 1).comp continuous_projection).continuousOn
  · exact ((continuous_apply 0).comp continuous_projection).continuousOn
  · exact hd

def parametrization (b : Bool) : OpenPartialHomeomorph (CoordinateSpace 2) Space where
  toFun := affineMap b
  invFun := affineCoords b
  source := univ
  target := affineTarget b
  map_source' z _ := affineMap_mem_target b z
  map_target' _ _ := mem_univ _
  left_inv' z _ := affineCoords_affineMap b z
  right_inv' x hx := affineMap_affineCoords b x hx
  open_source := isOpen_univ
  open_target := affineTarget_isOpen b
  continuousOn_toFun := (affineMap_continuous b).continuousOn
  continuousOn_invFun := affineCoords_continuousOn b

@[simp] theorem parametrization_apply (b : Bool) (z : CoordinateSpace 2) :
    parametrization b z = affineMap b z := rfl

@[simp] theorem parametrization_source (b : Bool) : (parametrization b).source = univ := rfl

@[simp] theorem parametrization_target (b : Bool) :
    (parametrization b).target = affineTarget b := rfl

theorem affineMap_isOpenEmbedding (b : Bool) : IsOpenEmbedding (affineMap b) :=
  (parametrization b).isOpenEmbedding rfl

theorem affineMap_jointly_surjective (x : Space) :
    ∃ b : Bool, ∃ z : CoordinateSpace 2, affineMap b z = x := by
  obtain h | h := RiemannSphere.standardCharts.covered (direction x)
  · exact ⟨false, affineCoords false x, affineMap_affineCoords false x h⟩
  · exact ⟨true, affineCoords true x, affineMap_affineCoords true x h⟩

end Wikipedia.HopfProblem.AffineBlowup
