/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Bilu.Section8Synthesis
import ErdosProblems.Erdos186.CFP.Bilu.SubspaceLattice
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Group.Pointwise

/-!
# Source data for Bilu Proposition 7.5

This file records equation (7.7) and the exact geometric output of
Proposition 7.4 which Proposition 7.5 estimates.  The body is kept in the
source product coordinates `E_m ⊕ E_r`; later an isometry identifies the
orthogonal projection with the product coordinates used by
`Section8Case2Canonical`.
-/

namespace Erdos186.CFP.Bilu.Proposition75Data

open MeasureTheory Set Module Submodule
open scoped BigOperators Pointwise RealInnerProductSpace

/-- Bilu's orthogonal product `E_m ⊕ E_r`, with the Hilbert `ℓ²` norm. -/
abbrev Ambient (m r : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))

/-- First coordinate of the Hilbert product. -/
abbrev head {m r : ℕ} (z : Ambient m r) : EuclideanSpace ℝ (Fin m) :=
  (WithLp.ofLp z).1

/-- Second coordinate of the Hilbert product. -/
abbrev tail {m r : ℕ} (z : Ambient m r) : EuclideanSpace ℝ (Fin r) :=
  (WithLp.ofLp z).2

/-- The standard product lattice `ℤ^m ⊕ ℤ^r` in the Hilbert product
coordinates. -/
noncomputable def ambientProductIntegralPoints (m r : ℕ) :
    Submodule ℤ (Ambient m r) :=
  ((SubspaceLattice.ambientIntegralPoints (n := m)).prod
      (SubspaceLattice.ambientIntegralPoints (n := r))).map
    (WithLp.linearEquiv 2 ℤ
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin r))).symm.toLinearMap

/-- Bilu's body `Omega`, equation (7.7).  We use non-strict inequalities;
this is the closed convex body with the same volume as the paper's open
version. -/
def distortionBody {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Set (Ambient m r) :=
  {z | head z ∈ (2 : ℝ) • B ∧
    ∀ i, |⟪head z, a i⟫ - tail z i| ≤ 1}

@[simp]
theorem mem_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    {z : Ambient m r} :
    z ∈ distortionBody B a ↔
      head z ∈ (2 : ℝ) • B ∧
        ∀ i, |⟪head z, a i⟫ - tail z i| ≤ 1 :=
  Iff.rfl

/-- The distortion body is convex whenever the original body is convex. -/
theorem convex_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : Convex ℝ B) (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    Convex ℝ (distortionBody B a) := by
  intro z hz w hw α β hα hβ hαβ
  refine ⟨?_, ?_⟩
  · exact (hB.smul (2 : ℝ)) hz.1 hw.1 hα hβ hαβ
  · intro i
    have hz' := hz.2 i
    have hw' := hw.2 i
    have hrewrite :
        ⟪head (α • z + β • w), a i⟫ - tail (α • z + β • w) i =
          α * (⟪head z, a i⟫ - tail z i) +
            β * (⟪head w, a i⟫ - tail w i) := by
      change
        ⟪α • head z + β • head w, a i⟫ -
            (α • tail z + β • tail w) i = _
      simp [inner_add_left, inner_smul_left]
      ring
    rw [hrewrite]
    calc
      |α * (⟪head z, a i⟫ - tail z i) +
          β * (⟪head w, a i⟫ - tail w i)| ≤
          |α * (⟪head z, a i⟫ - tail z i)| +
            |β * (⟪head w, a i⟫ - tail w i)| := abs_add_le _ _
      _ = α * |⟪head z, a i⟫ - tail z i| +
          β * |⟪head w, a i⟫ - tail w i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
      _ ≤ α * 1 + β * 1 := by gcongr
      _ = 1 := by linarith

/-- The distortion body is measurable whenever the original body is
measurable. -/
theorem measurableSet_distortionBody {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    (hB : MeasurableSet B) (a : Fin r → EuclideanSpace ℝ (Fin m)) :
    MeasurableSet (distortionBody B a) := by
  have hscaled : MeasurableSet ((2 : ℝ) • B) :=
    hB.const_smul₀ 2
  have hfirst : MeasurableSet
      {z : Ambient m r | head z ∈ (2 : ℝ) • B} := by
    apply hscaled.preimage
    fun_prop
  have hconstraint : ∀ i : Fin r, MeasurableSet
      {z : Ambient m r | |⟪head z, a i⟫ - tail z i| ≤ 1} := by
    intro i
    apply measurableSet_le
    · fun_prop
    · fun_prop
  simpa only [distortionBody, Set.ofPred_and, Set.ofPred_forall] using
    hfirst.inter (MeasurableSet.iInter hconstraint)

/-- Proposition 7.4 data attached to the body (7.7).  All equalities are
definitional/source bookkeeping; the substantive estimate to be proved is
the separate `Proposition75Conclusion` below. -/
structure GeometricData {m r : ℕ}
    (B : Set (EuclideanSpace ℝ (Fin m)))
    (a : Fin r → EuclideanSpace ℝ (Fin m)) where
  C0 : Submodule ℝ
    (Ambient m r)
  proper : C0 ≠ ⊤
  spans : Submodule.span ℝ
    ({z : C0 | (z : Ambient m r) ∈ distortionBody B a} ∩
      ((ambientProductIntegralPoints m r).comap
        (C0.subtype.restrictScalars ℤ) : Set C0)) = ⊤
  normal_tail_ne_zero : ∀ z :
      Ambient m r,
    z ∈ Submodule.orthogonal (𝕜 := ℝ) C0 → z ≠ 0 → tail z ≠ 0

/-- The section `B₀=C₀∩Ω`; unlike a defaulted structure field, this is
definitionally forced by the source data. -/
def GeometricData.B0 {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) : Set D.C0 :=
  {z | (z : Ambient m r) ∈ distortionBody B a}

/-- The literal lattice `C₀ ∩ ℤ^(m+r)`, transported to the subtype
`C₀`.  It is definitionally fixed, not an overridable witness field. -/
noncomputable def GeometricData.latticePoints {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) : Submodule ℤ D.C0 :=
  (ambientProductIntegralPoints m r).comap
    (D.C0.subtype.restrictScalars ℤ)

/-- Division-free version of Bilu equation (7.8).  `constant` is the
source's `c45(sigma)`, and `scale` is the positive power of `k / Vol B`.
-/
def Proposition75Conclusion {m r : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin m))}
    {a : Fin r → EuclideanSpace ℝ (Fin m)}
    (D : GeometricData B a) (constant scale : ENNReal) : Prop :=
  μHE[finrank ℝ D.C0] D.B0 ≤
    constant * volume B * scale *
      ENNReal.ofReal
        (ZLattice.covolume D.latticePoints μHE[finrank ℝ D.C0])

end Erdos186.CFP.Bilu.Proposition75Data

#print axioms Erdos186.CFP.Bilu.Proposition75Data.convex_distortionBody
#print axioms Erdos186.CFP.Bilu.Proposition75Data.measurableSet_distortionBody
