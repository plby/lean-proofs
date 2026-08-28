import Wikipedia.NoExoticSixSphere.FamilyFlatteningCoordinates

/-!
# The actual inverse flattening and its retained parameters

All identities hold on the genuine target of the constructed partial
diffeomorphism. Time and the last spatial coordinate are retained exactly;
the leading output is the new leading coordinate.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped ContDiff Manifold

namespace NoExoticSixSphere.FamilyFlattening

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : T → E × ℝ → E × F}

def Data.inverse (d : Data f) (r : (T × E) × ℝ) : E × (T × ℝ) :=
  d.coord.symm (flatOrder r)

def Data.target (d : Data f) : Opens ((T × E) × ℝ) :=
  ⟨flatOrder ⁻¹' d.coord.target, d.coord.open_target.preimage flatOrder.continuous⟩

def Data.flattened (d : Data f) (r : (T × E) × ℝ) : F :=
  tail f (d.inverse r)

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.inverse_mem_source (d : Data f) {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    d.inverse r ∈ d.coord.source :=
  d.coord.toOpenPartialHomeomorph.map_target hr

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.coord_inverse (d : Data f) {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    d.coord (d.inverse r) = flatOrder r :=
  d.coord.toOpenPartialHomeomorph.right_inv hr

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.inverse_parameters (d : Data f) {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    (d.inverse r).2 = (r.1.1, r.2) :=
  congrArg Prod.snd ((d.coord_apply (d.inverse r)).symm.trans (d.coord_inverse hr))

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.head_inverse (d : Data f) {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    head f (d.inverse r) = r.1.2 :=
  congrArg Prod.fst ((d.coord_apply (d.inverse r)).symm.trans (d.coord_inverse hr))

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.contDiffOn_inverse (d : Data f) :
    ContDiffOn ℝ ∞ d.inverse d.target :=
  d.coord.contMDiffOn_invFun.contDiffOn.comp
    (flatOrder (T := T) (E := E)).contDiff.contDiffOn (fun _ hr ↦ hr)

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.contDiffOn_flattened (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f) :
    ContDiffOn ℝ ∞ d.flattened d.target :=
  (contDiff_tail f hf).comp_contDiffOn d.contDiffOn_inverse

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ F] in
theorem Data.map_inverse (d : Data f) {r : (T × E) × ℝ} (hr : r ∈ d.target) :
    f r.1.1 ((d.inverse r).1, r.2) = (r.1.2, d.flattened r) := by
  have ht : (d.inverse r).2.1 = r.1.1 := congrArg Prod.fst (d.inverse_parameters hr)
  have hz : (d.inverse r).2.2 = r.2 := congrArg Prod.snd (d.inverse_parameters hr)
  rw [← ht, ← hz]
  exact Prod.ext (d.head_inverse hr) rfl

end NoExoticSixSphere.FamilyFlattening
