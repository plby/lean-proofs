import Wikipedia.HopfProblem.HolomorphicVectorFields

/-!
# The native holomorphic generator of an analytic complex-parameter family

A jointly holomorphic map `Φ : M × ℂ → M` with `Φ (x, 0) = x` gives an
analytic section of the original tangent bundle by differentiating the
time variable at zero. The proof applies the genuine tangent map to the
parameter-direction vector `(0, 1)` in the native tangent bundle of the
product. No group law, classification of flows, or replacement atlas is
assumed.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicVectorFields

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The actual parameter-direction vector along the zero-time inclusion. -/
private def timeDirection (x : M) :
    TangentBundle (𝓘(ℂ, E).prod 𝓘(ℂ)) (M × ℂ) :=
  ⟨(x, 0), (0, 1)⟩

private theorem timeDirection_holomorphic :
    ContMDiff 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ)).tangent ω (timeDirection E M) := by
  have hz : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E).tangent ω
      (fun x : M => (⟨x, 0⟩ : TangentBundle 𝓘(ℂ, E) M)) :=
    contMDiff_zeroSection ℂ (TangentSpace 𝓘(ℂ, E) : M → Type _)
  have ht : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ).tangent ω
      (fun _ : M => (⟨0, (1 : ℂ)⟩ : TangentBundle 𝓘(ℂ) ℂ)) := contMDiff_const
  have hp : ContMDiff (𝓘(ℂ, E).tangent.prod 𝓘(ℂ).tangent)
      (𝓘(ℂ, E).prod 𝓘(ℂ)).tangent ω
      (equivTangentBundleProd 𝓘(ℂ, E) M 𝓘(ℂ) ℂ).symm :=
    contMDiff_equivTangentBundleProd_symm
  exact hp.comp (hz.prodMk ht)

omit [IsManifold 𝓘(ℂ, E) ω M] in
/-- The partial time derivative is the total differential on the actual
parameter-direction vector in the product tangent space. -/
theorem timeDerivative_eq_joint (Φ : M × ℂ → M)
    (hΦ : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) ω Φ) (x : M) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ) =
      mfderiv (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) Φ (x, 0) (0, 1) := by
  erw [mfderiv_prod_eq_add_apply ((hΦ (x, 0)).mdifferentiableAt (by simp))]
  erw [map_zero, zero_add]

/-- The literal time derivative is holomorphic as a section of the
original tangent bundle, not merely as a coordinate-valued function. -/
theorem timeDerivative_section_holomorphic (Φ : M × ℂ → M)
    (hΦ : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) ω Φ)
    (hzero : ∀ x : M, Φ (x, 0) = x) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E).tangent ω
      (fun x : M => (⟨x,
        mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ)⟩ :
          TangentBundle 𝓘(ℂ, E) M)) := by
  have ht := (hΦ.contMDiff_tangentMap (m := ω) (by simp)).comp
    (timeDirection_holomorphic E M)
  have he : (fun x : M => (⟨x,
        mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ)⟩ :
          TangentBundle 𝓘(ℂ, E) M)) =
      tangentMap (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) Φ ∘ timeDirection E M := by
    funext x
    change (⟨x, mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ)⟩ :
      TangentBundle 𝓘(ℂ, E) M) =
        ⟨Φ (x, 0), mfderiv (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) Φ (x, 0) (0, 1)⟩
    rw [← timeDerivative_eq_joint E M Φ hΦ x, hzero x]
  rw [he]
  exact ht

/-- The native analytic generator of a jointly holomorphic family fixing
every point at time zero. The underlying vector is the literal time
derivative evaluated on `1 : ℂ`. -/
def timeGenerator (Φ : M × ℂ → M)
    (hΦ : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) ω Φ)
    (hzero : ∀ x : M, Φ (x, 0) = x) : Field E M where
  toFun x := mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ)
  contMDiff_toFun := timeDerivative_section_holomorphic E M Φ hΦ hzero

@[simp] theorem timeGenerator_apply (Φ : M × ℂ → M)
    (hΦ : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) ω Φ)
    (hzero : ∀ x : M, Φ (x, 0) = x) (x : M) :
    timeGenerator E M Φ hΦ hzero x =
      mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ) := rfl

variable (F N : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℂ, F) ω N]

/-- A holomorphic map intertwining two actual parameter families sends
their native generators to one another by its genuine differential. -/
theorem timeGenerator_naturality
    (Φ : M × ℂ → M)
    (hΦ : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ)) 𝓘(ℂ, E) ω Φ)
    (hΦ0 : ∀ x : M, Φ (x, 0) = x)
    (Ψ : N × ℂ → N)
    (hΨ : ContMDiff (𝓘(ℂ, F).prod 𝓘(ℂ)) 𝓘(ℂ, F) ω Ψ)
    (hΨ0 : ∀ y : N, Ψ (y, 0) = y)
    (g : M → N) (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ω g)
    (hcomm : ∀ x s, g (Φ (x, s)) = Ψ (g x, s)) (x : M) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x (timeGenerator E M Φ hΦ hΦ0 x) =
      timeGenerator F N Ψ hΨ hΨ0 (g x) := by
  change mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) g x
      (mfderiv 𝓘(ℂ) 𝓘(ℂ, E) (fun s : ℂ => Φ (x, s)) 0 (1 : ℂ)) =
    mfderiv 𝓘(ℂ) 𝓘(ℂ, F) (fun s : ℂ => Ψ (g x, s)) 0 (1 : ℂ)
  have hcurve : ContMDiff 𝓘(ℂ) 𝓘(ℂ, E) ω (fun s : ℂ => Φ (x, s)) :=
    hΦ.comp (contMDiff_const.prodMk contMDiff_id)
  have hcomp : g ∘ (fun s : ℂ => Φ (x, s)) = fun s => Ψ (g x, s) :=
    funext (hcomm x)
  calc
    _ = mfderiv 𝓘(ℂ) 𝓘(ℂ, F) (g ∘ (fun s : ℂ => Φ (x, s))) 0 (1 : ℂ) :=
      (mfderiv_comp_apply_of_eq 0 (hg.mdifferentiableAt (by simp))
        (hcurve.mdifferentiableAt (by simp)) (hΦ0 x) (1 : ℂ)).symm
    _ = _ := by rw [hcomp]

end Wikipedia.HopfProblem.HolomorphicVectorFields
