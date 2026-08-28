import Wikipedia.NoExoticSixSphere.SphereLevelEquations

/-!
# The actual Hilbert ambient inclusion of a product of spheres

The product keeps its original product manifold atlas. Its ambient space
is the genuine L2 product of the two Euclidean spaces. The inclusion and
the product radial retraction are smooth near the product of spheres,
and the retraction fixes the actual inclusion pointwise.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductSphereLevelEquations

variable {E G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

abbrev Ambient (E G : Type*) := WithLp 2 (E × G)

def inclusion (x : UnitSphere E × UnitSphere G) : Ambient E G :=
  WithLp.toLp 2 (x.1.val, x.2.val)

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ G] in
theorem inclusion_injective : Injective (inclusion (E := E) (G := G)) := by
  intro x y h
  exact Prod.ext (Subtype.ext (congrArg (fun p : Ambient E G ↦ p.fst) h))
    (Subtype.ext (congrArg (fun p : Ambient E G ↦ p.snd) h))

def retract (a : UnitSphere E × UnitSphere G) (v : Ambient E G) :
    UnitSphere E × UnitSphere G :=
  (SphereRadialRetraction.retract a.1 v.fst, SphereRadialRetraction.retract a.2 v.snd)

theorem retract_inclusion (a x : UnitSphere E × UnitSphere G) :
    retract a (inclusion x) = x := by
  apply Prod.ext
  · exact SphereRadialRetraction.retract_coe a.1 x.1
  · exact SphereRadialRetraction.retract_coe a.2 x.2

variable {m n : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  [Fact (Module.finrank ℝ G = n + 1)]

theorem contMDiff_inclusion :
    ContMDiff ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, Ambient E G) ∞ (inclusion (E := E) (G := G)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E G).symm.contDiff.contMDiff.comp
    (((contMDiff_coe_sphere (n := m) (m := ∞)).comp contMDiff_fst).prodMk_space
      ((contMDiff_coe_sphere (n := n) (m := ∞)).comp contMDiff_snd))

theorem contMDiffAt_retract (a x : UnitSphere E × UnitSphere G) :
    ContMDiffAt 𝓘(ℝ, Ambient E G) ((𝓡 m).prod (𝓡 n)) ∞ (retract a) (inclusion x) := by
  have hE : ContMDiffAt 𝓘(ℝ, E) (𝓡 m) ∞ (SphereRadialRetraction.retract a.1) x.1.val :=
    SphereRadialRetraction.contMDiffAt_retract a.1 (ne_zero_of_mem_unit_sphere x.1)
  have hG : ContMDiffAt 𝓘(ℝ, G) (𝓡 n) ∞ (SphereRadialRetraction.retract a.2) x.2.val :=
    SphereRadialRetraction.contMDiffAt_retract a.2 (ne_zero_of_mem_unit_sphere x.2)
  have he : ContDiff ℝ ∞ (WithLp.prodContinuousLinearEquiv 2 ℝ E G) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E G).contDiff
  exact (hE.comp (inclusion x) (he.fst.contMDiff (inclusion x))).prodMk
    (hG.comp (inclusion x) (he.snd.contMDiff (inclusion x)))

def inclusionDifferential (x : UnitSphere E × UnitSphere G) :
    (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ] Ambient E G :=
  mfderiv ((𝓡 m).prod (𝓡 n)) 𝓘(ℝ, Ambient E G) inclusion x

theorem inclusionDifferential_injective (x : UnitSphere E × UnitSphere G) :
    Injective (inclusionDifferential (m := m) (n := n) x) := by
  have he : retract x ∘ inclusion = id := funext (retract_inclusion x)
  have hc := mfderiv_comp x
    ((contMDiffAt_retract (m := m) (n := n) x x).mdifferentiableAt (by simp))
    ((contMDiff_inclusion (m := m) (n := n)).mdifferentiableAt (by simp))
  rw [he, mfderiv_id] at hc
  intro u v huv
  have h := congrArg
    (mfderiv 𝓘(ℝ, Ambient E G) ((𝓡 m).prod (𝓡 n)) (retract x) (inclusion x)) huv
  have hu := congrArg
    (fun L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦ L u) hc
  have hv := congrArg
    (fun L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) ↦ L v) hc
  exact hu.trans (h.trans hv.symm)

end NoExoticSixSphere.ProductSphereLevelEquations
