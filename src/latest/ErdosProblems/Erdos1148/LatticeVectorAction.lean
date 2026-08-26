import ErdosProblems.Erdos1148.PacketCuspHeight

/-! # Changing a modular lattice representative transports its integral vectors -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def frameRealVector (g : SL(2, ℝ)) (v : Fin 2 → ℝ) : Fin 2 → ℝ := g.toLin'.symm v

lemma frameRealVector_mul (g h : SL(2, ℝ)) (v : Fin 2 → ℝ) :
    frameRealVector (g * h) (g.toLin' v) = frameRealVector h v := by
  apply (g * h).toLin'.injective
  simp only [frameRealVector, LinearEquiv.apply_symm_apply, map_mul, LinearEquiv.mul_apply]

lemma integral_toLin_cast (γ : SL(2, ℤ)) (v : Fin 2 → ℤ) :
    (fun i => ((γ.toLin' v i : ℤ) : ℝ)) = (γ : SL(2, ℝ)).toLin' (fun i => (v i : ℝ)) := by
  ext i
  simp [Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec,
    Fin.sum_univ_two]

lemma frameRealVector_pair (g : SL(2, ℝ)) (u v : ℤ) :
    (frameRealVector g ![(u : ℝ), (v : ℝ)] 0, frameRealVector g ![(u : ℝ), (v : ℝ)] 1) =
      modularVector g u v := by
  simp [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply, Matrix.toLin'_apply,
    Matrix.mulVec, Fin.sum_univ_two, modularVector, Matrix.vecHead, Matrix.vecTail]

theorem modularVector_integral_change (γ : SL(2, ℤ)) (g : SL(2, ℝ)) (u v : ℤ) :
    modularVector ((γ : SL(2, ℝ)) * g) (γ.toLin' ![u, v] 0) (γ.toLin' ![u, v] 1) =
      modularVector g u v := by
  have hcast : ![((γ.toLin' ![u, v] 0 : ℤ) : ℝ), ((γ.toLin' ![u, v] 1 : ℤ) : ℝ)] =
      (γ : SL(2, ℝ)).toLin' ![(u : ℝ), (v : ℝ)] := by
    have h := integral_toLin_cast γ ![u, v]
    convert h using 1 <;> ext i <;> fin_cases i <;> rfl
  rw [← frameRealVector_pair, ← frameRealVector_pair, hcast,
    frameRealVector_mul]

lemma integral_toLin_pair_ne_zero (γ : SL(2, ℤ)) {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) :
    γ.toLin' ![u, v] 0 ≠ 0 ∨ γ.toLin' ![u, v] 1 ≠ 0 := by
  by_contra h
  push Not at h
  have hz : γ.toLin' ![u, v] = 0 := by
    ext i
    fin_cases i
    · exact h.1
    · exact h.2
  have hvec : ![u, v] = 0 := γ.toLin'.map_eq_zero_iff.mp hz
  have hu := congrFun hvec 0
  have hv := congrFun hvec 1
  exact huv.elim (fun h => h hu) (fun h => h hv)

theorem mem_modularCusp_iff_representative (g : SL(2, ℝ)) (H : ℝ) :
    modularMk g ∈ modularCusp H ↔
      ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ modularVectorLengthSq g u v < (H ^ 2)⁻¹ := by
  constructor
  · intro hx
    simp only [modularCusp, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq] at hx
    obtain ⟨u, v, huv, h, hshort, heq⟩ := hx
    obtain ⟨γ, hγ⟩ := (modularMk_eq_iff h g).mp heq
    refine ⟨γ.toLin' ![u, v] 0, γ.toLin' ![u, v] 1,
      integral_toLin_pair_ne_zero γ huv, ?_⟩
    rw [← hγ]
    simpa only [modularVectorLengthSq, modularVector_integral_change] using hshort
  · rintro ⟨u, v, huv, hshort⟩
    simp only [modularCusp, Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨u, v, huv, g, hshort, rfl⟩

end Erdos1148.DukeArithmetic
