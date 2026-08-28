import Wikipedia.HopfProblem.SingularMayerVietorisSmallChains
import Wikipedia.HopfProblem.SingularMayerVietorisQuasiIsoCriteria
import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionHomotopy
import Wikipedia.HopfProblem.SingularMayerVietorisSubdivisionSupport

/-!
# Small chains and actual singular homology

The comparison is proved on Mathlib's actual chain complexes. Subdivision
produces small representatives, and the subdivision homotopy supplies both
the comparison boundaries and small lifts of boundaries.
-/

noncomputable section

open CategoryTheory Set

namespace Wikipedia.HopfProblem.SingularMayerVietoris

open FirstHurewicz

variable {X : Type} [TopologicalSpace X]

/-- The algebraic small-chain comparison for a family of chain deformations.
The hypotheses are identities and support statements on actual chains, not
assumptions about homology or the inclusion being a quasi-isomorphism. -/
theorem smallInclusion_quasiIso_of_deformation (U V : Set X)
    (s : ∀ _k n : ℕ, Chains X n →ₗ[ℤ] Chains X n)
    (h : ∀ _k n : ℕ, Chains X n →ₗ[ℤ] Chains X (n + 1))
    (hs : ∀ k n, ∀ c : Chains X (n + 1),
      ((singularComplex X).d (n + 1) n).hom (s k (n + 1) c) =
        s k n (((singularComplex X).d (n + 1) n).hom c))
    (hh : ∀ k n, ∀ c : Chains X n,
      ((singularComplex X).d n (n - 1)).hom c = 0 →
        ((singularComplex X).d (n + 1) n).hom (h k n c) = c - s k n c)
    (hsmall : ∀ k n, ∀ c : Chains X n, c ∈ smallChainSubmodule U V n →
      h k n c ∈ smallChainSubmodule U V (n + 1))
    (heventually : ∀ n, ∀ c : Chains X n, ∃ k, s k n c ∈ smallChainSubmodule U V n) :
    QuasiIso (smallInclusion U V) := by
  apply ModuleHomology.quasiIso_of_injective_chain_conditions (smallInclusion U V)
  · intro n
    exact smallInclusion_f_injective U V n
  · intro n c hc
    obtain ⟨k, hk⟩ := heventually n c
    exact ⟨⟨s k n c, hk⟩, h k n c, hh k n c hc⟩
  · intro n c hc b hb
    have hc' : ((singularComplex X).d n (n - 1)).hom c.1 = 0 :=
      congrArg (fun z : (smallComplex U V).X (n - 1) => z.1) hc
    change ((singularComplex X).d (n + 1) n).hom b = c.1 at hb
    obtain ⟨k, hk⟩ := heventually (n + 1) b
    refine ⟨⟨s k (n + 1) b + h k n c.1,
      (smallChainSubmodule U V (n + 1)).add_mem hk (hsmall k n c.1 c.2)⟩, ?_⟩
    apply Subtype.ext
    change ((singularComplex X).d (n + 1) n).hom
      (s k (n + 1) b + h k n c.1) = c.1
    rw [map_add, hs, hb, hh k n c.1 hc']
    rw [← add_sub_assoc, add_comm, add_sub_cancel_right]

/-- The actual small-chain inclusion for an open two-set cover is a
quasi-isomorphism in every degree, including degree zero. -/
theorem smallInclusion_quasiIso (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) :
    QuasiIso (smallInclusion U V) := by
  apply smallInclusion_quasiIso_of_deformation U V (subdivision X) (subdivisionHomotopy X)
  · exact fun k n c => subdivision_boundary k n c
  · exact fun k n c hc => subdivisionHomotopy_boundary_of_cycle k n c hc
  · exact fun k n c hc => subdivisionHomotopy_mem_small U V k n c hc
  · intro n c
    obtain ⟨N, hN⟩ := eventually_subdivision_mem_small U V hU hV hcover n c
    exact ⟨N, hN N le_rfl⟩

/-- The proved small-chain comparison as an isomorphism of the actual
categorical homology objects. Its forward map is induced by inclusion. -/
def smallHomologyIso (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    (smallComplex U V).homology n ≅ (singularComplex X).homology n := by
  letI := smallInclusion_quasiIso U V hU hV hcover
  exact isoOfQuasiIsoAt (smallInclusion U V) n

@[simp] theorem smallHomologyIso_hom (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    (smallHomologyIso U V hU hV hcover n).hom =
      HomologicalComplex.homologyMap (smallInclusion U V) n := rfl

@[simp] theorem smallHomologyIso_hom_inv (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    HomologicalComplex.homologyMap (smallInclusion U V) n ≫
      (smallHomologyIso U V hU hV hcover n).inv = 𝟙 _ :=
  (smallHomologyIso U V hU hV hcover n).hom_inv_id

@[simp] theorem smallHomologyIso_inv_hom (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    (smallHomologyIso U V hU hV hcover n).inv ≫
      HomologicalComplex.homologyMap (smallInclusion U V) n = 𝟙 _ :=
  (smallHomologyIso U V hU hV hcover n).inv_hom_id

/-- The same comparison as an integral linear equivalence, without replacing
either of the actual homology groups. -/
def smallHomologyEquiv (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    (smallComplex U V).homology n ≃ₗ[ℤ] (singularComplex X).homology n :=
  (smallHomologyIso U V hU hV hcover n).toLinearEquiv

@[simp] theorem smallHomologyEquiv_toLinearMap (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ) :
    (smallHomologyEquiv U V hU hV hcover n).toLinearMap =
      (HomologicalComplex.homologyMap (smallInclusion U V) n).hom := rfl

@[simp] theorem smallHomologyEquiv_apply (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ)
    (c : (smallComplex U V).homology n) :
    smallHomologyEquiv U V hU hV hcover n c =
      (HomologicalComplex.homologyMap (smallInclusion U V) n).hom c := rfl

/-- On concrete cycle classes the comparison is the literal inclusion
of small singular cycles in singular cycles. -/
theorem smallHomologyEquiv_cycleClass (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ) (n : ℕ)
    (c : ModuleHomology.Cycle (smallComplex U V) n) :
    smallHomologyEquiv U V hU hV hcover n (ModuleHomology.cycleClass (smallComplex U V) n c) =
      ModuleHomology.cycleClass (singularComplex X) n
        (ModuleHomology.mapCycles (smallInclusion U V) n c) :=
  ModuleHomology.homologyMap_cycleClass (smallInclusion U V) n c

end Wikipedia.HopfProblem.SingularMayerVietoris
