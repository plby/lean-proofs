import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalPatchBasic

/-!
# Literal local agreement of the patched singular cochain

The closed-refinement selector is locally controlled. When the original
cochains agree by literal restriction near a point, patching therefore
agrees there as an original cochain, before any sheafification.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable {X : TopCat.{0}} (A : AddCommGrpCat.{0}) (n : ℕ)
  {ι : Type} (U : ι → Opens X) (R : ClosedRefinement U)
  (t : ∀ i, Cochains (U i) A n)

/-- A controlled neighborhood on which the genuine representatives agree
is a neighborhood on which the patched original cochain agrees with them. -/
theorem patchedCochain_restrict_of_compatible
    (x : X) (W : Opens X) (j : ι) (hj : W ≤ U j)
    (hcontrol : ∀ y ∈ W, ∀ i, y ∈ R.support i → x ∈ R.support i)
    (hW : ∀ i, x ∈ R.support i → W ≤ U i)
    (hcompat : ∀ i (hi : x ∈ R.support i),
      (cochainPresheaf X A n).map (homOfLE (hW i hi)).op (t i) =
        (cochainPresheaf X A n).map (homOfLE hj).op (t j)) :
    restrictGlobalCochain A n (patchedCochain A n U R t) W =
      (cochainPresheaf X A n).map (homOfLE hj).op (t j) := by
  apply cochain_ext W A n
  intro σ
  let τ : SingularSimplex X n :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(W, X)).comp σ
  let i := patchIndex n U R τ
  let v : Simplex n := stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))
  have hi : x ∈ R.support i :=
    hcontrol (τ v) (σ v).property i (R.mem_support_index _)
  have hτ : range τ ⊆ U i := by
    rintro _ ⟨z, rfl⟩
    exact hW i hi (σ z).property
  have hvalues := congrArg
    (fun c : Cochains W A n => c (simplexChain W n σ)) (hcompat i hi)
  calc
    restrictGlobalCochain A n (patchedCochain A n U R t) W
        (simplexChain W n σ) =
      patchedCochain A n U R t (simplexChain X n τ) :=
        restrictGlobalCochain_simplex A n _ W σ
    _ = t i (simplexChain (U i) n (simplexInOpen n τ (U i) hτ)) :=
      patchedCochain_simplex_of_subset A n U R t τ hτ
    _ = ((cochainPresheaf X A n).map (homOfLE (hW i hi)).op (t i))
        (simplexChain W n σ) :=
      (cochainPresheaf_map_simplex X A n (homOfLE (hW i hi)) (t i) σ).symm
    _ = ((cochainPresheaf X A n).map (homOfLE hj).op (t j))
        (simplexChain W n σ) := hvalues

/-- Germwise agreement of the original representatives supplies an
actual neighborhood on which the patched cochain equals the selected
representative, by equality of original cochains. -/
theorem exists_neighborhood_patchedCochain_eq
    (x : X) (j : ι) (hxj : x ∈ R.support j)
    (hlocal : ∀ i, x ∈ R.support i →
      ∃ V : Opens X, x ∈ V ∧ ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (cochainPresheaf X A n).map f.op (t i) =
          (cochainPresheaf X A n).map g.op (t j)) :
    ∃ (W : Opens X), x ∈ W ∧ ∃ (f : W ⟶ U j),
      restrictGlobalCochain A n (patchedCochain A n U R t) W =
        (cochainPresheaf X A n).map f.op (t j) := by
  classical
  have hall : ∀ i, ∃ V : Opens X, x ∈ V ∧
      (x ∈ R.support i → ∃ (f : V ⟶ U i) (g : V ⟶ U j),
        (cochainPresheaf X A n).map f.op (t i) =
          (cochainPresheaf X A n).map g.op (t j)) := by
    intro i
    by_cases hi : x ∈ R.support i
    · obtain ⟨V, hxV, f, g, heq⟩ := hlocal i hi
      exact ⟨V, hxV, fun _ => ⟨f, g, heq⟩⟩
    · exact ⟨⊤, by simp, fun h => (hi h).elim⟩
  choose V hxV hV using hall
  obtain ⟨W, hxW, hWV, hcontrol⟩ :=
    R.exists_controlled_neighborhood x V (fun i _ => hxV i)
  have hWU : ∀ i, x ∈ R.support i → W ≤ U i := by
    intro i hi
    exact (hWV i hi).trans (leOfHom (hV i hi).choose)
  have hcompat : ∀ i (hi : x ∈ R.support i),
      (cochainPresheaf X A n).map (homOfLE (hWU i hi)).op (t i) =
        (cochainPresheaf X A n).map (homOfLE (hWU j hxj)).op (t j) := by
    intro i hi
    obtain ⟨f, g, heq⟩ := hV i hi
    have h := congrArg
      (fun c => (cochainPresheaf X A n).map (homOfLE (hWV i hi)).op c) heq
    let P := cochainPresheaf X A n
    let k : W ⟶ V i := homOfLE (hWV i hi)
    have hf := congrArg
      (fun l : P.obj (op (U i)) ⟶ P.obj (op W) => l (t i))
      (P.map_comp f.op k.op)
    have hg := congrArg
      (fun l : P.obj (op (U j)) ⟶ P.obj (op W) => l (t j))
      (P.map_comp g.op k.op)
    exact hf.trans (h.trans hg.symm)
  exact ⟨W, hxW, homOfLE (hWU j hxj),
    patchedCochain_restrict_of_compatible A n U R t x W j (hWU j hxj)
      hcontrol hWU hcompat⟩

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
