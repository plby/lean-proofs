import Wikipedia.NoExoticSixSphere.CompactExhaustionHomology
import Wikipedia.NoExoticSixSphere.JamesCompactFactorization

/-!
# Finite-stage representation and zero detection for James homology

The compact-factorization theorem is applied to the actual James stages,
and to their products with any fixed space. The product-stage subspace is
identified with the literal product. This proves finite-stage homology
representation without assuming that homology or products preserve a
topological direct limit.
-/

noncomputable section

open Set Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.James.HomologyStages

variable {X : Type} [TopologicalSpace X] [T1Space X] (x₀ : X)

def inclusion (k : ℕ) : C(stage x₀ k, Space X x₀) := subtypeInclusion (stage x₀ k)

def transition {k l : ℕ} (hkl : k ≤ l) : C(stage x₀ k, stage x₀ l) :=
  ContinuousMap.inclusion (stage_mono x₀ hkl)

omit [T1Space X] in
theorem inclusion_transition {k l : ℕ} (hkl : k ≤ l) :
    (inclusion x₀ l).comp (transition x₀ hkl) = inclusion x₀ k := rfl

omit [T1Space X] in
theorem transition_trans {k l m : ℕ} (hkl : k ≤ l) (hlm : l ≤ m) :
    (transition x₀ hlm).comp (transition x₀ hkl) = transition x₀ (hkl.trans hlm) := rfl

theorem exhaustive (K : Set (Space X x₀)) (hK : IsCompact K) : ∃ k, K ⊆ stage x₀ k :=
  exists_stage_of_isCompact x₀ hK

theorem exists_homology_lift (d : ℕ) (a : SingularHomology (Space X x₀) d) :
    ∃ k, ∃ b : SingularHomology (stage x₀ k) d, singularHomologyMap (inclusion x₀ k) d b = a :=
  CompactExhaustionHomology.exists_homology_lift (stage x₀) (exhaustive x₀) d a

theorem exists_later_zero (k d : ℕ) (a : SingularHomology (stage x₀ k) d)
    (ha : singularHomologyMap (inclusion x₀ k) d a = 0) :
    ∃ m, ∃ hkm : k ≤ m, singularHomologyMap (transition x₀ hkm) d a = 0 :=
  CompactExhaustionHomology.exists_later_zero (stage x₀) (exhaustive x₀)
    (fun _ _ h ↦ stage_mono x₀ h) k d a ha

variable (P : Type) [TopologicalSpace P]

def productStage (k : ℕ) : Set (P × Space X x₀) := {p | p.2 ∈ stage x₀ k}

def productHomeomorph (k : ℕ) : (P × stage x₀ k) ≃ₜ productStage x₀ P k where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2, p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

def productInclusion (k : ℕ) : C(P × stage x₀ k, P × Space X x₀) :=
  (ContinuousMap.id P).prodMap (inclusion x₀ k)

def productTransition {k l : ℕ} (hkl : k ≤ l) : C(P × stage x₀ k, P × stage x₀ l) :=
  (ContinuousMap.id P).prodMap (transition x₀ hkl)

omit [T1Space X] in
theorem productInclusion_transition {k l : ℕ} (hkl : k ≤ l) :
    (productInclusion x₀ P l).comp (productTransition x₀ P hkl) = productInclusion x₀ P k := rfl

theorem product_exhaustive (K : Set (P × Space X x₀)) (hK : IsCompact K) :
    ∃ k, K ⊆ productStage x₀ P k := by
  obtain ⟨k, hk⟩ := exhaustive x₀ (Prod.snd '' K) (hK.image continuous_snd)
  exact ⟨k, fun p hp ↦ hk ⟨p, hp, rfl⟩⟩

theorem exists_product_homology_lift (d : ℕ) (a : SingularHomology (P × Space X x₀) d) :
    ∃ k, ∃ b : SingularHomology (P × stage x₀ k) d,
      singularHomologyMap (productInclusion x₀ P k) d b = a := by
  obtain ⟨k, b, hb⟩ := CompactExhaustionHomology.exists_homology_lift
    (productStage x₀ P) (product_exhaustive x₀ P) d a
  let E := homeomorphHomologyEquiv (productHomeomorph x₀ P k) d
  refine ⟨k, E.symm b, ?_⟩
  have hcomp : (subtypeInclusion (productStage x₀ P k)).comp
      ⟨productHomeomorph x₀ P k, (productHomeomorph x₀ P k).continuous⟩ =
        productInclusion x₀ P k := rfl
  rw [← hcomp, singularHomologyMap_comp]
  change singularHomologyMap (subtypeInclusion (productStage x₀ P k)) d (E (E.symm b)) = a
  rw [E.apply_symm_apply]
  exact hb

end NoExoticSixSphere.James.HomologyStages
