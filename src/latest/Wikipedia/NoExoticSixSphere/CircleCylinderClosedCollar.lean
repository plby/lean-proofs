import Wikipedia.NoExoticSixSphere.CircleCylinderClosedCollarMap

/-!
# The actual closed time band is homeomorphic to interval times endpoints

The explicit closed collar map is a continuous bijection from a compact
space to a Hausdorff space. This proves continuity of its true inverse;
the underlying map and its literal seam-time coordinate remain unchanged.
-/

noncomputable section

open Function Set
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem compactSpace_endpoints : CompactSpace (Endpoints d) := by
  let : CompactSpace {x : Sphere m // d.leftMap x = b} :=
    isCompact_iff_compactSpace.mp
      (isClosed_eq d.leftMap.continuous continuous_const).isCompact
  let : CompactSpace {x : Sphere m // d.rightMap x = b} :=
    isCompact_iff_compactSpace.mp
      (isClosed_eq d.rightMap.continuous continuous_const).isCompact
  infer_instance

abbrev ClosedTimeBand := {p : Fiber d // time d p ∈ Icc (-collarWidth d) (collarWidth d)}

def closedBandMap : C(CollarInterval d × Endpoints d, ClosedTimeBand d) where
  toFun p := ⟨closedCollarMap d p, (time_closedCollarMap d p).symm ▸ p.1.property⟩
  continuous_toFun := (closedCollarMap d).continuous.subtype_mk _

theorem closedBandMap_bijective : Bijective (closedBandMap d) := by
  constructor
  · intro p q h
    exact closedCollarMap_injective d (congrArg Subtype.val h)
  · intro p
    obtain ⟨q, hq⟩ := closedCollarMap_covers d p.val p.property
    exact ⟨q, Subtype.ext hq⟩

def closedCollar : CollarInterval d × Endpoints d ≃ₜ ClosedTimeBand d := by
  letI := compactSpace_endpoints d
  let e := Equiv.ofBijective (closedBandMap d) (closedBandMap_bijective d)
  exact Continuous.homeoOfEquivCompactToT2 (f := e) (closedBandMap d).continuous

theorem closedCollar_apply (p : CollarInterval d × Endpoints d) :
    (closedCollar d p).val = closedCollarMap d p := rfl

theorem time_closedCollar (p : CollarInterval d × Endpoints d) :
    time d (closedCollar d p).val = p.1.val := time_closedCollarMap d p

theorem closedCollar_symm_time (p : ClosedTimeBand d) :
    ((closedCollar d).symm p).1.val = time d p.val := by
  have h := time_closedCollar d ((closedCollar d).symm p)
  rw [(closedCollar d).apply_symm_apply] at h
  exact h.symm

theorem closedCollar_zero (x : Endpoints d) :
    (closedCollar d
      (⟨0, neg_nonpos.mpr (collarWidth_pos d).le, (collarWidth_pos d).le⟩, x)).val =
        endpointsMap d x := closedCollarMap_zero d x

end NoExoticSixSphere.CircleCylinder
