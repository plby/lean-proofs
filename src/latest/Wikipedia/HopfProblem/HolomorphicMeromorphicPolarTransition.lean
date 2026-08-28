import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarTransitionRegular
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarTransitionStalk

/-!
# Native holomorphic transition units from associated holomorphic germs

The actual fraction of two holomorphic sections is regular and invertible
at every point when their germs are associated and the denominator germs
are nonzero. Its canonical regular representative is the desired native
holomorphic transition function, including at zeros of the denominator.
The product identity and uniqueness are proved in the original stalks.
-/

noncomputable section

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I ω M]

/-- A holomorphic section with nonzero germ at every point can be cancelled,
even when it has zeros as an ordinary function. -/
theorem section_mul_right_cancel {U : Opens M}
    {q u v : HolomorphicFunctionSheaf.Section I M U}
    (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0) (h : u * q = v * q) : u = v := by
  apply ofHolomorphic_injective I M U
  apply section_ext
  intro x
  rw [ofHolomorphic_apply, ofHolomorphic_apply]
  have hq' : sectionGerm I M U x q ≠ 0 :=
    fun hz ↦ hq x ((sectionGerm_eq_zero_iff I M U x q).mp hz)
  apply mul_right_cancel₀ hq'
  simpa only [map_mul] using congrArg (sectionGerm I M U x) h

variable {U : Opens M} (p q : HolomorphicFunctionSheaf.Section I M U)
  (hq : ∀ x : U, holomorphicGerm I M U x q ≠ 0)
  (hassoc : ∀ x : U, Associated (holomorphicGerm I M U x p) (holomorphicGerm I M U x q))

/-- The transition function is the native regular representative of the
actual meromorphic fraction, not the total pointwise division `p / q`. -/
def transitionUnit : HolomorphicFunctionSheaf.Section I M U :=
  holomorphicRepresentative I M (ofFraction I M U p q hq)
    (fraction_regularAt_of_associated I M p q hq hassoc)

@[simp] theorem transitionUnit_apply (x : U) :
    transitionUnit I M p q hq hassoc x = value I M (ofFraction I M U p q hq) x := rfl

/-- Exact meromorphic germs of the constructed native transition function. -/
theorem transitionUnit_germ (x : U) :
    sectionGerm I M U x (transitionUnit I M p q hq hassoc) = fraction I M U p q x :=
  holomorphicRepresentative_germ I M (ofFraction I M U p q hq)
    (fraction_regularAt_of_associated I M p q hq hassoc) x

theorem ofHolomorphic_transitionUnit :
    ofHolomorphic I M U (transitionUnit I M p q hq hassoc) = ofFraction I M U p q hq :=
  ofHolomorphic_holomorphicRepresentative I M (ofFraction I M U p q hq)
    (fraction_regularAt_of_associated I M p q hq hassoc)

theorem transitionUnit_ne_zero (x : U) : transitionUnit I M p q hq hassoc x ≠ 0 :=
  fraction_value_ne_zero_of_associated I M p q hq hassoc x

/-- The original numerator equals the constructed holomorphic unit times
the denominator, as literal native holomorphic sections. -/
theorem transitionUnit_mul : p = transitionUnit I M p q hq hassoc * q := by
  apply ofHolomorphic_injective I M U
  apply section_ext
  intro x
  have hq' : sectionGerm I M U x q ≠ 0 :=
    fun hz ↦ hq x ((sectionGerm_eq_zero_iff I M U x q).mp hz)
  rw [ofHolomorphic_apply, ofHolomorphic_apply, map_mul,
    transitionUnit_germ, fraction]
  exact (div_mul_cancel₀ _ hq').symm

theorem transitionUnit_mul_apply (x : U) :
    p x = transitionUnit I M p q hq hassoc x * q x :=
  congrArg (fun f : HolomorphicFunctionSheaf.Section I M U ↦ f x)
    (transitionUnit_mul I M p q hq hassoc)

/-- On the denominator's cozero set this is ordinary pointwise division. -/
theorem transitionUnit_apply_of_ne_zero (x : U) (hqx : q x ≠ 0) :
    transitionUnit I M p q hq hassoc x = p x / q x := by
  apply (eq_div_iff hqx).mpr
  exact (transitionUnit_mul_apply I M p q hq hassoc x).symm

/-- A transition section satisfying the product identity is unique. -/
theorem transitionUnit_unique {v : HolomorphicFunctionSheaf.Section I M U}
    (hv : p = v * q) : v = transitionUnit I M p q hq hassoc :=
  section_mul_right_cancel I M hq (hv.symm.trans (transitionUnit_mul I M p q hq hassoc))

/-- The transition function is a unit of the actual native section ring.
Its inverse is its pointwise reciprocal, proved holomorphic in the same atlas. -/
def transitionUnits : (HolomorphicFunctionSheaf.Section I M U)ˣ where
  val := transitionUnit I M p q hq hassoc
  inv := ⟨fun x ↦ (transitionUnit I M p q hq hassoc x)⁻¹, by
    intro x
    exact ((contDiffAt_inv ℂ (transitionUnit_ne_zero I M p q hq hassoc x)).contMDiffAt).comp x
      (transitionUnit I M p q hq hassoc).contMDiff.contMDiffAt⟩
  val_inv := by
    apply ContMDiffMap.ext
    intro x
    exact mul_inv_cancel₀ (transitionUnit_ne_zero I M p q hq hassoc x)
  inv_val := by
    apply ContMDiffMap.ext
    intro x
    exact inv_mul_cancel₀ (transitionUnit_ne_zero I M p q hq hassoc x)

@[simp] theorem transitionUnits_val :
    (transitionUnits I M p q hq hassoc : HolomorphicFunctionSheaf.Section I M U) =
      transitionUnit I M p q hq hassoc := rfl

theorem transitionUnit_isUnit : IsUnit (transitionUnit I M p q hq hassoc) :=
  ⟨transitionUnits I M p q hq hassoc, rfl⟩

include hq hassoc in
/-- Associated nonzero denominator germs produce a unique genuine native
holomorphic transition function, nowhere zero on the whole overlap. -/
theorem existsUnique_transitionUnit :
    ∃! v : HolomorphicFunctionSheaf.Section I M U, (∀ x : U, v x ≠ 0) ∧ p = v * q := by
  refine ⟨transitionUnit I M p q hq hassoc,
    ⟨transitionUnit_ne_zero I M p q hq hassoc, transitionUnit_mul I M p q hq hassoc⟩, ?_⟩
  intro v hv
  exact transitionUnit_unique I M p q hq hassoc hv.2

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarTransition
