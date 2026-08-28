import Wikipedia.NoExoticSixSphere.SmoothTransport

/-!
# Smooth projection transport on a compact region of an ambient vector space

The operator family is smooth on an actual open neighborhood of the region.
Invertibility and the intertwining equation are required on the region itself.
This permits transport over closed disks without pretending that a closed
disk has a boundaryless manifold structure.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An actual ambient operator transport, smooth near the prescribed source region. -/
structure SmoothRangeTransportOn (K : Set E) (P Q : E → F →L[ℝ] F) where
  toFun : E → F →L[ℝ] F
  neighborhood : Set E
  open_neighborhood : IsOpen neighborhood
  contains : K ⊆ neighborhood
  smooth : ContDiffOn ℝ ∞ toFun neighborhood
  invertible : ∀ x ∈ K, (toFun x).IsInvertible
  intertwines : ∀ x ∈ K, Q x * toFun x = toFun x * P x

namespace SmoothRangeTransportOn

variable {K : Set E} {P Q R : E → F →L[ℝ] F}

def refl (K : Set E) (P : E → F →L[ℝ] F) : SmoothRangeTransportOn K P P where
  toFun _ := 1
  neighborhood := univ
  open_neighborhood := isOpen_univ
  contains := subset_univ _
  smooth := contDiffOn_const
  invertible _ _ := ⟨ContinuousLinearEquiv.refl ℝ F, rfl⟩
  intertwines _ _ := by rw [mul_one, one_mul]

def trans (a : SmoothRangeTransportOn K P Q) (b : SmoothRangeTransportOn K Q R) :
    SmoothRangeTransportOn K P R where
  toFun x := b.toFun x * a.toFun x
  neighborhood := a.neighborhood ∩ b.neighborhood
  open_neighborhood := a.open_neighborhood.inter b.open_neighborhood
  contains := fun _ hx => ⟨a.contains hx, b.contains hx⟩
  smooth := (b.smooth.mono inter_subset_right).clm_comp (a.smooth.mono inter_subset_left)
  invertible x hx := (b.invertible x hx).comp (a.invertible x hx)
  intertwines x hx := by
    calc
      R x * (b.toFun x * a.toFun x) = (R x * b.toFun x) * a.toFun x := (mul_assoc _ _ _).symm
      _ = (b.toFun x * Q x) * a.toFun x := by rw [b.intertwines x hx]
      _ = b.toFun x * (Q x * a.toFun x) := mul_assoc _ _ _
      _ = b.toFun x * (a.toFun x * P x) := by rw [a.intertwines x hx]
      _ = (b.toFun x * a.toFun x) * P x := (mul_assoc _ _ _).symm

variable [CompleteSpace F]

/-- Reverse the transport on a possibly smaller actual open neighborhood of the region. -/
def symm (a : SmoothRangeTransportOn K P Q) : SmoothRangeTransportOn K Q P where
  toFun x := (a.toFun x).inverse
  neighborhood := a.neighborhood ∩ {x | (a.toFun x).IsInvertible}
  open_neighborhood := a.smooth.continuousOn.isOpen_inter_preimage a.open_neighborhood
    ContinuousLinearEquiv.isOpen
  contains := fun x hx => ⟨a.contains hx, a.invertible x hx⟩
  smooth := by
    intro x hx
    exact (hx.2.contDiffAt_map_inverse.comp x
      (a.smooth.contDiffAt (a.open_neighborhood.mem_nhds hx.1))).contDiffWithinAt
  invertible x hx := (a.invertible x hx).inverse
  intertwines x hx := by
    apply ContinuousLinearMap.ext
    intro v
    change P x ((a.toFun x).inverse v) = (a.toFun x).inverse (Q x v)
    apply (a.invertible x hx).injective
    rw [(a.invertible x hx).self_apply_inverse]
    have h := congrArg (fun L : F →L[ℝ] F => L ((a.toFun x).inverse v)) (a.intertwines x hx)
    change Q x (a.toFun x ((a.toFun x).inverse v)) =
      a.toFun x (P x ((a.toFun x).inverse v)) at h
    rw [(a.invertible x hx).self_apply_inverse] at h
    exact h.symm

omit [CompleteSpace F] in
/-- The transport identifies the actual operator ranges at every point of the region. -/
theorem map_range (a : SmoothRangeTransportOn K P Q) (x : E) (hx : x ∈ K) :
    Submodule.map (a.toFun x).toLinearMap (P x).range = (Q x).range := by
  rw [← LinearMap.range_comp]
  have hlin : (a.toFun x).toLinearMap.comp (P x).toLinearMap =
      (Q x).toLinearMap.comp (a.toFun x).toLinearMap :=
    congrArg ContinuousLinearMap.toLinearMap (a.intertwines x hx).symm
  rw [hlin]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (a.invertible x hx).surjective)

/-- The explicit nearby-projection intertwiner is smooth on the intersection of the two
given neighborhoods and supplies transport whenever it is invertible on the region. -/
def ofProjections (hP : ∀ x ∈ K, IsIdempotentElem (P x))
    (hQ : ∀ x ∈ K, IsIdempotentElem (Q x))
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hKU : K ⊆ U) (hKV : K ⊆ V)
    (hsP : ContDiffOn ℝ ∞ P U) (hsQ : ContDiffOn ℝ ∞ Q V)
    (hinv : ∀ x ∈ K, (NoExoticSixSphere.projectionIntertwiner (P x) (Q x)).IsInvertible) :
    SmoothRangeTransportOn K P Q where
  toFun x := NoExoticSixSphere.projectionIntertwiner (P x) (Q x)
  neighborhood := U ∩ V
  open_neighborhood := hU.inter hV
  contains := fun _ hx => ⟨hKU hx, hKV hx⟩
  smooth := ((hsQ.mono inter_subset_right).clm_comp (hsP.mono inter_subset_left)).add
    ((contDiffOn_const.sub (hsQ.mono inter_subset_right)).clm_comp
      (contDiffOn_const.sub (hsP.mono inter_subset_left)))
  invertible := hinv
  intertwines x hx :=
    NoExoticSixSphere.projectionIntertwiner_intertwines (P x) (Q x) (hP x hx) (hQ x hx)

end SmoothRangeTransportOn

end Wikipedia.SmoothSixDPoincare.DiskFraming
