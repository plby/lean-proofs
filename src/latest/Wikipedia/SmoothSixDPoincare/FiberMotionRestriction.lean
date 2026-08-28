import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Restrict a normal-coordinate-preserving diffeomorphism to a linear submodel

A split linear inclusion of normal models is invariant under any map that
fixes every normal coordinate. The actual inverse has the same invariance,
so restriction gives a genuine smooth diffeomorphism, not only an embedding.
-/

noncomputable section

open Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FiberRestriction

variable {X U V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def embed (i : U →L[ℝ] V) : (X × U) →L[ℝ] (X × V) :=
  (ContinuousLinearMap.id ℝ X).prodMap i

def project (r : V →L[ℝ] U) : (X × V) →L[ℝ] (X × U) :=
  (ContinuousLinearMap.id ℝ X).prodMap r

theorem project_embed (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : LeftInverse r i)
    (z : X × U) : project r (embed i z) = z :=
  Prod.ext rfl (hi z.2)

theorem embed_project_of_normal (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : LeftInverse r i)
    {z : X × V} {w : X × U} (hz : z.2 = i w.2) : embed i (project r z) = z := by
  apply Prod.ext
  · rfl
  · change i (r z.2) = z.2
    rw [hz, hi]

/-- Restriction uses the original diffeomorphism and its actual inverse. -/
def restrict (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : LeftInverse r i)
    (d : Diffeomorph 𝓘(ℝ, X × V) 𝓘(ℝ, X × V) (X × V) (X × V) ∞)
    (hnormal : ∀ z, (d z).2 = z.2) :
    Diffeomorph 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) (X × U) (X × U) ∞ where
  toEquiv := {
    toFun := fun z => project r (d (embed i z))
    invFun := fun z => project r (d.symm (embed i z))
    left_inv := by
      intro z
      have hfix := embed_project_of_normal i r hi (w := z) (hnormal (embed i z))
      change project r (d.symm (embed i (project r (d (embed i z))))) = z
      rw [hfix, d.symm_apply_apply, project_embed i r hi]
    right_inv := by
      intro z
      have hnormalInv : (d.symm (embed i z)).2 = i z.2 := by
        have he := hnormal (d.symm (embed i z))
        rw [d.apply_symm_apply] at he
        exact he.symm
      have hfix := embed_project_of_normal i r hi (w := z) hnormalInv
      change project r (d (embed i (project r (d.symm (embed i z))))) = z
      rw [hfix, d.apply_symm_apply, project_embed i r hi] }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞
      (fun z => project r (d (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.contMDiff.comp (embed i).contDiff.contMDiff)
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞
      (fun z => project r (d.symm (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.symm.contMDiff.comp (embed i).contDiff.contMDiff)

theorem restrict_apply (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : LeftInverse r i)
    (d : Diffeomorph 𝓘(ℝ, X × V) 𝓘(ℝ, X × V) (X × V) (X × V) ∞)
    (hnormal : ∀ z, (d z).2 = z.2) (z : X × U) :
    restrict i r hi d hnormal z = project r (d (embed i z)) := rfl

end Wikipedia.SmoothSixDPoincare.FiberRestriction
