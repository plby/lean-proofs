import ErdosProblems.Erdos587.HooleyFiniteIndexSpan

/-! # Whole-lattice coordinates for a finite-index coefficient subgroup -/

open scoped BigOperators

namespace Erdos587.GeneralizedAP

noncomputable def deltaFiniteIndexBasis {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    [Γ.FiniteIndex] : Module.Basis (Fin d) ℤ Γ.toIntSubmodule := by
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Γ.toIntSubmodule)
  have hdim : Module.finrank ℤ Γ.toIntSubmodule = d := by
    change Module.finrank ℤ Γ = d
    rw [Γ.finrank_eq_of_finiteIndex, Module.finrank_pi]
    simp
  have hn : n = d := by simpa only [Module.finrank_eq_card_basis b, Fintype.card_fin] using hdim
  exact b.reindex (finCongr hn)

noncomputable def deltaLatticeEmbedding {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) : (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℤ) :=
  Γ.toIntSubmodule.subtype.comp b.equivFun.symm.toLinearMap

lemma deltaLatticeEmbedding_mem {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) (x : Fin d → ℤ) :
    deltaLatticeEmbedding Γ b x ∈ Γ := (b.equivFun.symm x).property

lemma deltaLatticeEmbedding_range {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) (x : Fin d → ℤ) :
    (∃ y, deltaLatticeEmbedding Γ b y = x) ↔ x ∈ Γ := by
  constructor
  · rintro ⟨y, rfl⟩
    exact deltaLatticeEmbedding_mem Γ b y
  · intro hx
    refine ⟨b.equivFun ⟨x, hx⟩, ?_⟩
    change (b.equivFun.symm (b.equivFun ⟨x, hx⟩)).val = x
    rw [b.equivFun.symm_apply_apply]

lemma deltaLatticeEmbedding_injective {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) :
    Function.Injective (deltaLatticeEmbedding Γ b) :=
  Subtype.val_injective.comp b.equivFun.symm.injective

lemma deltaLatticeEmbedding_real_surjective {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    [Γ.FiniteIndex] (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) :
    Function.Surjective (intLinearMapRealExtension (deltaLatticeEmbedding Γ b)) := by
  let q := deltaLatticeEmbedding Γ b
  let qR := intLinearMapRealExtension q
  have hindex : (Γ.index : ℝ) ≠ 0 := by
    exact_mod_cast (AddSubgroup.FiniteIndex.index_ne_zero (H := Γ))
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (Pi.basisFun ℝ (Fin d)).span_eq]
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := (deltaLatticeEmbedding_range Γ b _).mpr
    (Γ.nsmul_index_mem (Pi.single i (1 : ℤ)))
  have hscaled : (Γ.index : ℝ) • Pi.single i (1 : ℝ) ∈ LinearMap.range qR := by
    refine ⟨intCastVec y, ?_⟩
    rw [intLinearMapRealExtension_intCastVec, hy]
    funext j
    simp [intCastVec, Pi.single_apply]
  have hh := (LinearMap.range qR).smul_mem (Γ.index : ℝ)⁻¹ hscaled
  have hmem : Pi.single i (1 : ℝ) ∈ LinearMap.range qR := by
    simpa only [inv_smul_smul₀ hindex] using hh
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  simpa only [Pi.basisFun_apply, qR, q] using hz

noncomputable def deltaLatticeRealEquiv {d : ℕ} (Γ : AddSubgroup (Fin d → ℤ))
    [Γ.FiniteIndex] (b : Module.Basis (Fin d) ℤ Γ.toIntSubmodule) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) :=
  LinearEquiv.ofBijective (intLinearMapRealExtension (deltaLatticeEmbedding Γ b))
    ⟨LinearMap.injective_iff_surjective.mpr (deltaLatticeEmbedding_real_surjective Γ b),
      deltaLatticeEmbedding_real_surjective Γ b⟩

end Erdos587.GeneralizedAP
