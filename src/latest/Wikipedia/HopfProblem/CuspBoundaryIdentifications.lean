import Wikipedia.HopfProblem.CuspComponentProjection
import Wikipedia.HopfProblem.ToricRayIncidence

/-!
# The opposite boundary identifications

On the component `E₀`, the curve meeting `E_v` is carried to the curve meeting
`E_{-v}` by the exact twisted lattice translation whose shear is `-v`.
This gives a homeomorphism of these actual subspaces which leaves their
images in the cusp quotient unchanged.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricSpace ToricFan

def componentBoundary (v : Fin 2 → ℤ) : Set (rayDivisor 0) :=
  {x | (x : Space) ∈ rayDivisor v}

def oppositeBoundaryMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : componentBoundary v) : componentBoundary (-v) :=
  ⟨⟨twistedTranslate C (cuspVector v) (x.1 : Space), by
      rw [twistedTranslate_mem_rayDivisor, cuspVector_cuspVector]
      simp only [zero_sub, neg_neg]
      exact x.2⟩, by
    change twistedTranslate C (cuspVector v) (x.1 : Space) ∈ rayDivisor (-v)
    rw [twistedTranslate_mem_rayDivisor, cuspVector_cuspVector, sub_self]
    exact x.1.2⟩

def oppositeBoundaryEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) :
    componentBoundary v ≃ componentBoundary (-v) where
  toFun := oppositeBoundaryMap C v
  invFun y := ⟨⟨twistedTranslate C (-cuspVector v) (y.1 : Space), by
      rw [twistedTranslate_mem_rayDivisor, cuspVector_neg, cuspVector_cuspVector,
        neg_neg, zero_sub]
      exact y.2⟩, by
    change twistedTranslate C (-cuspVector v) (y.1 : Space) ∈ rayDivisor v
    rw [twistedTranslate_mem_rayDivisor, cuspVector_neg, cuspVector_cuspVector,
      neg_neg, sub_self]
    exact y.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change twistedTranslate C (-cuspVector v)
      (twistedTranslate C (cuspVector v) (x.1 : Space)) = (x.1 : Space)
    rw [twistedTranslate_add]
    simp
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change twistedTranslate C (cuspVector v)
      (twistedTranslate C (-cuspVector v) (x.1 : Space)) = (x.1 : Space)
    rw [twistedTranslate_add]
    simp

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

@[simp] theorem componentProjection_oppositeBoundaryMap (v : Fin 2 → ℤ)
    (x : componentBoundary v) :
    componentProjection C ε hε (oppositeBoundaryMap C v x).1 =
      componentProjection C ε hε x.1 := by
  have he : componentLift ε hε (oppositeBoundaryMap C v x).1 =
      tubeTranslate C (disc ε) (cuspVector v) (componentLift ε hε x.1) := rfl
  change quotientMap C ε (componentLift ε hε (oppositeBoundaryMap C v x).1) = _
  rw [he, quotientMap_translate]
  rfl

theorem componentProjection_oppositeBoundary_image (v : Fin 2 → ℤ) :
    componentProjection C ε hε '' componentBoundary v =
      componentProjection C ε hε '' componentBoundary (-v) := by
  apply subset_antisymm
  · rintro q ⟨x, hx, rfl⟩
    exact ⟨(oppositeBoundaryMap C v ⟨x, hx⟩).1,
      (oppositeBoundaryMap C v ⟨x, hx⟩).2,
      componentProjection_oppositeBoundaryMap C ε hε v ⟨x, hx⟩⟩
  · rintro q ⟨y, hy, rfl⟩
    let x := (oppositeBoundaryEquiv C v).symm ⟨y, hy⟩
    refine ⟨x.1, x.2, ?_⟩
    have he : oppositeBoundaryMap C v x = ⟨y, hy⟩ :=
      (oppositeBoundaryEquiv C v).apply_symm_apply _
    have hp := componentProjection_oppositeBoundaryMap C ε hε v x
    rw [he] at hp
    exact hp.symm

variable (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))

include hε hC in
theorem central_twistedTranslate_continuous (v : Fin 2 → ℤ) :
    Continuous (fun x : rayDivisor 0 => twistedTranslate C v (x : Space)) := by
  exact continuous_subtype_val.comp
    ((tubeTranslate_holomorphic C (disc ε) v hC).continuous.comp
      (componentLift_continuous ε hε))

def oppositeBoundaryHomeomorph (v : Fin 2 → ℤ) :
    componentBoundary v ≃ₜ componentBoundary (-v) where
  toEquiv := oppositeBoundaryEquiv C v
  continuous_toFun :=
    (((central_twistedTranslate_continuous C ε hε hC (cuspVector v)).comp
      continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun :=
    (((central_twistedTranslate_continuous C ε hε hC (-cuspVector v)).comp
      continuous_subtype_val).subtype_mk _).subtype_mk _

end Wikipedia.HopfProblem.CuspQuotient
