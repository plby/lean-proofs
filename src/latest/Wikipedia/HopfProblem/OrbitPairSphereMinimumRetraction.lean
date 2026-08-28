import Wikipedia.HopfProblem.OrbitPairSphereMinimumPolygonSpace

/-!
# A continuous neighborhood retraction onto minimum sphere polygons

One chosen interior vertex determines a tangent direction whenever its
orthogonal projection is nonzero. Resampling that direction gives an actual
minimum polygon. Every minimum polygon belongs to this open domain and is
fixed by the resulting retraction.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere GLOrthonormalization SphereVertexSpace SphereSemicircle

variable {n m : ℕ}

def minimumRetractionDomain (a b : Sphere n) (j : Fin m) : Set (Space n m) :=
  admissible (costDomain n) a b m ∩ {v | (v j).val ∈ directionDomain a}

theorem isOpen_minimumRetractionDomain (a b : Sphere n) (j : Fin m) :
    IsOpen (minimumRetractionDomain a b j) :=
  (isOpen_admissible (costDomain n) a b m).inter
    ((isOpen_directionDomain a).preimage (continuous_subtype_val.comp (continuous_apply j)))

def nearbyDirection (a b : Sphere n) (j : Fin m) :
    C(minimumRetractionDomain a b j, Direction a) :=
  (directionRetraction a).comp
    { toFun v := ⟨(v.val j).val, v.2.2⟩
      continuous_toFun :=
        (continuous_subtype_val.comp
          ((continuous_apply j).comp continuous_subtype_val)).subtype_mk _ }

variable (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : b.val = -a.val)
    (hmesh : ∀ i : Fin (m + 1), Real.pi ^ 2 * (τ i.succ - τ i.castSucc) < Real.pi ^ 2)
    (j : Fin m)

include hτ hzero hone hanti hmesh

theorem semicircle_mem_minimumRetractionDomain (y : Direction a) :
    semicircleVertices a τ y ∈ minimumRetractionDomain a b j :=
  ⟨(semicircleVertices_mem_minimumSet a b τ hτ hzero hone hanti hmesh y).1,
    curve_mem_directionDomain a y (interior_time_mem τ hτ hzero hone j)⟩

theorem nearbyDirection_semicircle (y : Direction a) :
    nearbyDirection a b j ⟨semicircleVertices a τ y,
      semicircle_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hmesh j y⟩ = y :=
  directionRetraction_curve a y (interior_time_mem τ hτ hzero hone j)

def minimumNeighborhoodRetraction : C(minimumRetractionDomain a b j, minimumSet a b τ) :=
  (minimumParametrization a b τ hτ hzero hone hanti hmesh).comp (nearbyDirection a b j)

theorem minimumSet_subset_retractionDomain :
    minimumSet a b τ ⊆ minimumRetractionDomain a b j := by
  intro v hv
  obtain ⟨y, hy⟩ := minimumParametrization_surjective a b τ hτ hzero hone hanti hmesh ⟨v, hv⟩
  have he : semicircleVertices a τ y = v := congrArg Subtype.val hy
  rw [← he]
  exact semicircle_mem_minimumRetractionDomain a b τ hτ hzero hone hanti hmesh j y

theorem minimumNeighborhoodRetraction_eq_self (v : minimumSet a b τ) :
    minimumNeighborhoodRetraction a b τ hτ hzero hone hanti hmesh j
      ⟨v.val, minimumSet_subset_retractionDomain a b τ hτ hzero hone hanti hmesh j v.2⟩ = v := by
  obtain ⟨y, rfl⟩ := minimumParametrization_surjective a b τ hτ hzero hone hanti hmesh v
  change minimumParametrization a b τ hτ hzero hone hanti hmesh
    (nearbyDirection a b j ⟨semicircleVertices a τ y, _⟩) = _
  rw [nearbyDirection_semicircle a b τ hτ hzero hone hanti hmesh j]

def minimumDirection : C(minimumSet a b τ, Direction a) :=
  (nearbyDirection a b j).comp
    { toFun v := ⟨v.val,
        minimumSet_subset_retractionDomain a b τ hτ hzero hone hanti hmesh j v.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }

def directionMinimumHomeomorph : Direction a ≃ₜ minimumSet a b τ where
  toFun := minimumParametrization a b τ hτ hzero hone hanti hmesh
  invFun := minimumDirection a b τ hτ hzero hone hanti hmesh j
  left_inv y := nearbyDirection_semicircle a b τ hτ hzero hone hanti hmesh j y
  right_inv v := minimumNeighborhoodRetraction_eq_self a b τ hτ hzero hone hanti hmesh j v
  continuous_toFun := (minimumParametrization a b τ hτ hzero hone hanti hmesh).continuous
  continuous_invFun := (minimumDirection a b τ hτ hzero hone hanti hmesh j).continuous

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
