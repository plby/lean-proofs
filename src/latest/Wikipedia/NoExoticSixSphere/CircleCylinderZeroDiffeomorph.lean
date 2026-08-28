import Wikipedia.NoExoticSixSphere.CircleCylinderEndpointSum
import Wikipedia.NoExoticSixSphere.RegularFiberIdentification

/-!
# The actual seam is diffeomorphic to the original endpoint disjoint union

The seam time is regular in the compact native circle-double fiber.
Its native zero atlas and the two original endpoint atlases are retained.
The actual endpoint-sum immersion parametrizes the complete zero fiber,
so its smooth inverse follows from the native regular-fiber theorem.
-/

noncomputable section

open Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def timeMap : C(Fiber d, ℝ) :=
  ⟨time d, contMDiff_seam.continuous.comp (continuous_fst.comp continuous_subtype_val)⟩

abbrev TimeZero := {p : Fiber d // time d p = 0}

theorem time_dimension_eq (k : ℕ) :
    finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = finrank ℝ ℝ + k := by
  simp only [finrank_euclideanSpace_fin, finrank_self]
  omega

@[instance_reducible]
def timeZeroAtlas (k : ℕ) (hd : m = n + k) :
    ChartedSpace (EuclideanSpace ℝ (Fin k)) (TimeZero d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  exact regularFiberAtlas (timeMap d) (contMDiff_time d k hd) 0 (regular_time_zero d k hd)
    k (time_dimension_eq k)

theorem timeZero_isManifold (k : ℕ) (hd : m = n + k) :
    letI := timeZeroAtlas d k hd;
    IsManifold (𝓡 k) ∞ (TimeZero d) := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  exact regularFiber_isManifold (timeMap d) (contMDiff_time d k hd) 0
    (regular_time_zero d k hd) k (time_dimension_eq k)

def endpointsDiffeomorph (k : ℕ) (hd : m = n + k) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    Endpoints d ≃ₘ⟮𝓡 k, 𝓡 k⟯ TimeZero d := by
  let := fiberAtlas d k hd
  let := fiber_isManifold d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := regularFiber_isManifold d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  let := regularFiber_isManifold d.rightMap d.smooth_right b d.regular_right k (by simpa using hd)
  let := timeZeroAtlas d k hd
  exact diffeomorphToRegularFiber (timeMap d) (contMDiff_time d k hd) 0
    (regular_time_zero d k hd) k (time_dimension_eq k) (endpointsMap d)
    (contMDiff_endpointsMap d k hd) (endpointsMap_injective d)
    (mfderiv_endpointsMap_injective d k hd) (time_eq_zero_iff_endpoints d)

theorem endpointsDiffeomorph_val (k : ℕ) (hd : m = n + k) (p : Endpoints d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k (by simpa using hd);
    letI := timeZeroAtlas d k hd;
    (endpointsDiffeomorph d k hd p).val = endpointsMap d p := rfl

end NoExoticSixSphere.CircleCylinder
