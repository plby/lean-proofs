import ErdosProblems.Erdos117.ScalarCliques

/-!
# Transversal cliques for isotropic subspaces

Dual vectors to an isotropic family can be corrected by a triangular sum to
give a constant-pairing clique. This avoids assuming an extension of that
family to a symplectic basis.
-/

namespace Erdos117

open Module
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_dual_vectors [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (U : Submodule K V) {ι : Type*} (b : Basis ι K U) :
    ∃ x : ι → V, ∀ i (y : U), B (x i) y = b.coord i y := by
  have hinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Subspace.dual_finrank_eq])).mp hinj
  have h (i : ι) : ∃ x : V, ∀ y : U, B x y = b.coord i y := by
    obtain ⟨φ, hφ⟩ := Subspace.dualRestrict_surjective (W := U) (b.coord i)
    obtain ⟨x, hx⟩ := hsurj φ
    refine ⟨x, fun y => ?_⟩
    rw [hx]
    exact LinearMap.congr_fun hφ y
  exact ⟨fun i => (h i).choose, fun i => (h i).choose_spec⟩

noncomputable def transversalCorrection {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V) (i : Fin d) : V :=
  ∑ j ∈ Finset.Iio i, (1 - B (x j) (x i)) • y j

noncomputable def transversalFamily {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V) : Option (Fin d) → V
  | none => ∑ j, y j
  | some i => x i + transversalCorrection B x y i

theorem transversalCorrection_pairing_right {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0) (i j : Fin d) :
    B (x i) (transversalCorrection B x y j) =
      if i < j then 1 - B (x i) (x j) else 0 := by
  classical
  simp [transversalCorrection, hxy]

theorem transversalCorrection_pairing_isotropic {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hyy : ∀ i j, B (y i) (y j) = 0) (i j : Fin d) :
    B (transversalCorrection B x y i) (y j) = 0 := by
  classical
  simp [transversalCorrection, LinearMap.sum_apply, LinearMap.smul_apply, hyy]

theorem transversalCorrection_pairing {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hyy : ∀ i j, B (y i) (y j) = 0) (i j : Fin d) :
    B (transversalCorrection B x y i) (transversalCorrection B x y j) = 0 := by
  classical
  simp [transversalCorrection, LinearMap.sum_apply, LinearMap.smul_apply, hyy]

theorem transversalFamily_pairing_some {d : ℕ}
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
    (hyy : ∀ i j, B (y i) (y j) = 0) {i j : Fin d} (hij : i < j) :
    B (transversalFamily B x y (some i)) (transversalFamily B x y (some j)) = 1 := by
  have hji : ¬j < i := not_lt_of_ge (le_of_lt hij)
  have hc : B (transversalCorrection B x y i) (x j) = 0 := by
    rw [← halt.neg_eq, transversalCorrection_pairing_right B x y hxy, if_neg hji, neg_zero]
  simp only [transversalFamily, map_add, LinearMap.add_apply,
    transversalCorrection_pairing_right B x y hxy, if_pos hij, hc,
    transversalCorrection_pairing B x y hyy, add_zero]
  ring

theorem transversalFamily_pairing_none {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
    (hyy : ∀ i j, B (y i) (y j) = 0) (i : Fin d) :
    B (transversalFamily B x y (some i)) (transversalFamily B x y none) = 1 := by
  classical
  simp [transversalFamily, LinearMap.add_apply, hxy,
    transversalCorrection_pairing_isotropic B x y hyy]

theorem transversalFamily_nonorthogonal {d : ℕ}
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
    (hyy : ∀ i j, B (y i) (y j) = 0) :
    NonorthogonalFamily B (transversalFamily B x y) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      rw [← halt.neg_eq, transversalFamily_pairing_none B x y hxy hyy]
      exact neg_ne_zero.mpr one_ne_zero
  | some i =>
    cases j with
    | none =>
      rw [transversalFamily_pairing_none B x y hxy hyy]
      exact one_ne_zero
    | some j =>
      have hne : i ≠ j := fun h => hij (congrArg Option.some h)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [transversalFamily_pairing_some B halt x y hxy hyy hlt]
        exact one_ne_zero
      · rw [← halt.neg_eq, transversalFamily_pairing_some B halt x y hxy hyy hgt]
        exact neg_ne_zero.mpr one_ne_zero

theorem transversalFamily_pairing_vector {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
    (hyy : ∀ i j, B (y i) (y j) = 0) (i : Option (Fin d)) (j : Fin d) :
    B (transversalFamily B x y i) (y j) = if i = some j then 1 else 0 := by
  classical
  cases i with
  | none => simp [transversalFamily, LinearMap.sum_apply, hyy]
  | some i =>
    simp [transversalFamily, LinearMap.add_apply, hxy,
      transversalCorrection_pairing_isotropic B x y hyy]

/-- The triangular clique has distinct cosets modulo the entire isotropic
subspace, not just modulo the span of the chosen vectors. -/
theorem transversalFamily_distinct_cosets {d : ℕ}
    (B : LinearMap.BilinForm K V) (x y : Fin d → V)
    (hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0)
    (U : Submodule K V) (hy : ∀ i, y i ∈ U)
    (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0) :
    ∀ i j, i ≠ j → transversalFamily B x y i - transversalFamily B x y j ∉ U := by
  have hyy : ∀ i j, B (y i) (y j) = 0 := fun i j => hU _ (hy i) _ (hy j)
  intro i j hij hmem
  have hpair (k : Fin d) :
      (if i = some k then (1 : K) else 0) = if j = some k then 1 else 0 := by
    have hz := hU _ hmem _ (hy k)
    rw [LinearMap.BilinForm.sub_left,
      transversalFamily_pairing_vector B x y hxy hyy,
      transversalFamily_pairing_vector B x y hxy hyy] at hz
    exact sub_eq_zero.mp hz
  cases i with
  | none =>
    cases j with
    | none => exact hij rfl
    | some j => simpa using hpair j
  | some i =>
    cases j with
    | none => simpa using hpair i
    | some j =>
      have hne : j ≠ i := fun h => hij (congrArg Option.some h.symm)
      simpa [hne] using hpair i

/-- The linear-algebra input to Lemma 5.4, with both the clique and its
transversality proved from the isotropic-subspace hypothesis. -/
theorem exists_transversal_clique [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (halt : B.IsAlt) (hB : B.Nondegenerate)
    (U : Submodule K V) (hU : ∀ u ∈ U, ∀ v ∈ U, B u v = 0)
    {d : ℕ} (hd : d ≤ finrank K U) :
    ∃ f : Fin (d + 1) → V, NonorthogonalFamily B f ∧
      ∀ i j, i ≠ j → f i - f j ∉ U := by
  classical
  let b := finBasis K U
  obtain ⟨a, ha⟩ := exists_dual_vectors B hB U b
  let x : Fin d → V := fun i => a (Fin.castLE hd i)
  let y : Fin d → V := fun i => b (Fin.castLE hd i)
  have hxy : ∀ i j, B (x i) (y j) = if i = j then 1 else 0 := by
    intro i j
    dsimp [x, y]
    rw [ha]
    simp [Finsupp.single_apply, eq_comm]
  have hy : ∀ i, y i ∈ U := fun i => (b (Fin.castLE hd i)).2
  have hyy : ∀ i j, B (y i) (y j) = 0 := fun i j => hU _ (hy i) _ (hy j)
  let e : Option (Fin d) ≃ Fin (d + 1) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨transversalFamily B x y ∘ e.symm, ?_, ?_⟩
  · exact (transversalFamily_nonorthogonal B halt x y hxy hyy).comp e.symm.injective
  · intro i j hij
    exact transversalFamily_distinct_cosets B x y hxy U hy hU _ _
      (fun h => hij (e.symm.injective h))

end Erdos117
