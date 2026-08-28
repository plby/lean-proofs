import Wikipedia.HopfProblem.OrbitPairSphereVertexSpace
import Wikipedia.NoExoticSixSphere.SphereNormalization

/-!
# Normalized interpolation between nearby sphere polygons

The open pair domain requires each corresponding pair of unit vertices to
have ambient distance less than one. The actual joining segments are then
nonzero at all homotopy times. Their normalizations depend continuously on
both vertex lists and time and fix every diagonal pair.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace

open NoExoticSixSphere GLOrthonormalization

variable {n m : ℕ}

def interpolationDomain (n m : ℕ) : Set (Space n m × Space n m) :=
  {p | ∀ j, dist (p.2 j).val (p.1 j).val < 1}

theorem isOpen_interpolationDomain (n m : ℕ) : IsOpen (interpolationDomain n m) := by
  change IsOpen {p : Space n m × Space n m | ∀ j, dist (p.2 j).val (p.1 j).val < 1}
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  exact isOpen_lt
    ((continuous_subtype_val.comp ((continuous_apply j).comp continuous_snd)).dist
      (continuous_subtype_val.comp ((continuous_apply j).comp continuous_fst))) continuous_const

theorem diagonal_mem_interpolationDomain (v : Space n m) :
    (v, v) ∈ interpolationDomain n m := by
  intro j
  simp only [dist_self, zero_lt_one]

def interpolate (t : I) (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    Space n m := fun j =>
  ⟨NormedSpace.normalize ((v j).val + (t : ℝ) • ((w j).val - (v j).val)), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (nearby_segment_ne_zero (v j) (w j).val (h j) t)⟩

theorem interpolate_zero (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 0 v w h = v := by
  funext j
  apply Subtype.ext
  change NormedSpace.normalize ((v j).val + (0 : ℝ) • ((w j).val - (v j).val)) = (v j).val
  simpa only [zero_smul, add_zero] using
    NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (v j))

theorem interpolate_one (v w : Space n m) (h : (v, w) ∈ interpolationDomain n m) :
    interpolate 1 v w h = w := by
  funext j
  apply Subtype.ext
  change NormedSpace.normalize ((v j).val + (1 : ℝ) • ((w j).val - (v j).val)) = (w j).val
  simpa only [one_smul, ← add_sub_assoc, add_sub_cancel_left] using
    NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (w j))

theorem interpolate_self (t : I) (v : Space n m) (h : (v, v) ∈ interpolationDomain n m) :
    interpolate t v v h = v := by
  funext j
  apply Subtype.ext
  change NormedSpace.normalize ((v j).val + (t : ℝ) • ((v j).val - (v j).val)) = (v j).val
  simpa only [sub_self, smul_zero, add_zero] using
    NormedSpace.normalize_eq_self_of_norm_eq_one (ClosedHemisphere.unit_norm (v j))

theorem continuous_interpolate {X : Type*} [TopologicalSpace X]
    (p q : X → Space n m) (hp : Continuous p) (hq : Continuous q)
    (hpair : ∀ x, (p x, q x) ∈ interpolationDomain n m) :
    Continuous (fun z : I × X => interpolate z.1 (p z.2) (q z.2) (hpair z.2)) := by
  apply continuous_pi
  intro j
  let f : C(X, Sphere n) := ⟨fun x => p x j, (continuous_apply j).comp hp⟩
  let g : C(X, Vector (n + 1)) :=
    ⟨fun x => (q x j).val, continuous_subtype_val.comp ((continuous_apply j).comp hq)⟩
  exact (nearbyNormalizationHomotopy f g (fun x => hpair x j)).continuous

theorem interpolate_eq_left_of_eq (t : I) (v w : Space n m)
    (h : (v, w) ∈ interpolationDomain n m) (he : w = v) : interpolate t v w h = v := by
  subst w
  exact interpolate_self t v h

end Wikipedia.HopfProblem.OrbitPair.SphereVertexSpace
