import Wikipedia.HopfProblem.DegreeCollapseRadialSphereMap
import Wikipedia.HopfProblem.DegreeCollapseHopfBlockCoordinates

/-!
# Adding actual Euclidean coordinates to a sphere map

The radial extension acts in the first summand and the second summand
is unchanged. The resulting sphere map has that same formula as its
radial extension. Associativity of adding two summands is an exact
map identity under the original Hilbert-sum isometry.
-/

noncomputable section

open scoped Topology
open NoExoticSixSphere

namespace Wikipedia.HopfProblem.DegreeCollapse.RadialSphereJoin

open RadialSphereMap HopfBlockCoordinates

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def vector (f : C(UnitSphere E, UnitSphere F)) (x : WithLp 2 (E × G)) : WithLp 2 (F × G) :=
  WithLp.toLp 2 (extend f x.fst, x.snd)

omit [NormedSpace ℝ G] in
theorem vector_norm (f : C(UnitSphere E, UnitSphere F)) (x : WithLp 2 (E × G)) :
    ‖vector f x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
  change ‖extend f x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2
  rw [extend_norm]

omit [NormedSpace ℝ G] in
theorem vector_zero (f : C(UnitSphere E, UnitSphere F)) : vector (G := G) f 0 = 0 := by
  change WithLp.toLp 2 (extend f 0, (0 : G)) = 0
  rw [extend_zero]
  rfl

theorem vector_smul_nonneg (f : C(UnitSphere E, UnitSphere F))
    (c : ℝ) (hc : 0 ≤ c) (x : WithLp 2 (E × G)) : vector f (c • x) = c • vector f x := by
  change WithLp.toLp 2 (extend f (c • x.fst), c • x.snd) = _
  rw [extend_smul_nonneg f c hc]
  rfl

omit [NormedSpace ℝ G] in
theorem continuous_vector (f : C(UnitSphere E, UnitSphere F)) :
    Continuous (vector (G := G) f) :=
  (WithLp.prod_continuous_toLp 2 F G).comp
    (((continuous_extend f).comp (WithLp.continuous_fst 2 E G)).prodMk
      (WithLp.continuous_snd 2 E G))

omit [NormedSpace ℝ G] in
theorem vector_mem_sphere (f : C(UnitSphere E, UnitSphere F))
    (x : UnitSphere (WithLp 2 (E × G))) : vector f x.val ∈ UnitSphere (WithLp 2 (F × G)) := by
  rw [mem_sphere_zero_iff_norm, vector_norm]
  exact mem_sphere_zero_iff_norm.mp x.property

def sphereMap (f : C(UnitSphere E, UnitSphere F)) :
    C(UnitSphere (WithLp 2 (E × G)), UnitSphere (WithLp 2 (F × G))) :=
  ⟨fun x ↦ ⟨vector f x.val, vector_mem_sphere f x⟩,
    ((continuous_vector f).comp continuous_subtype_val).subtype_mk _⟩

theorem extend_sphereMap (f : C(UnitSphere E, UnitSphere F)) (x : WithLp 2 (E × G)) :
    extend (sphereMap f) x = vector f x :=
  extend_unique (sphereMap f) (vector f) (vector_zero f) (vector_smul_nonneg f)
    (fun _ ↦ rfl) x

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem sphereMap_assoc (f : C(UnitSphere E, UnitSphere F))
    (x : UnitSphere (WithLp 2 (WithLp 2 (E × G) × H))) :
    unitSphereCoordinates (LinearIsometryEquiv.withLpProdAssoc 2 ℝ F G H)
      (sphereMap (G := H) (sphereMap (G := G) f) x) =
    sphereMap (G := WithLp 2 (G × H)) f
      (unitSphereCoordinates (LinearIsometryEquiv.withLpProdAssoc 2 ℝ E G H) x) := by
  apply Subtype.ext
  change WithLp.toLp 2 ((extend (sphereMap f) x.val.fst).fst,
    WithLp.toLp 2 ((extend (sphereMap f) x.val.fst).snd, x.val.snd)) =
      WithLp.toLp 2 (extend f x.val.fst.fst, WithLp.toLp 2 (x.val.fst.snd, x.val.snd))
  rw [extend_sphereMap]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.RadialSphereJoin
