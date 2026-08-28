import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPresheafBasic

/-!
# Selector endomorphisms of actual singular cochains

A selector on the ambient space assigns each singular simplex according
to its first vertex. The corresponding projections are additive for
arbitrary abelian coefficients and commute with open restrictions. For
a finite selector range they sum to the identity. On an open set avoiding
one selector value, that projection vanishes on all actual cochains.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.FineCochains

open FirstHurewicz

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)
variable {ι : Type*} (sel : X → ι) (i : ι)

/-- The actual cochain projection selecting simplices by their first
ambient vertex. No structure on the selector or coefficients is needed. -/
def selectorCochainEnd (U : Opens X) : Cochains U A n →+ Cochains U A n := by
  classical
  exact
    { toFun φ := cochainFromValues U A n (fun σ =>
        if sel (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))).val = i then
          φ (simplexChain U n σ) else 0)
      map_zero' := by
        apply cochain_ext U A n
        intro σ
        simp only [cochainFromValues_simplex, AddMonoidHom.zero_apply, ite_self]
      map_add' φ ψ := by
        apply cochain_ext U A n
        intro σ
        simp only [cochainFromValues_simplex, AddMonoidHom.add_apply]
        split <;> simp }

open Classical in
/-- The selector projection has its specified value on each original
singular simplex generator. -/
@[simp] theorem selectorCochainEnd_simplex (U : Opens X) (φ : Cochains U A n)
    (σ : SingularSimplex U n) :
    selectorCochainEnd X A n sel i U φ (simplexChain U n σ) =
      if sel (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))).val = i then
        φ (simplexChain U n σ) else 0 := by
  classical
  exact cochainFromValues_simplex U A n _ σ

/-- The first ambient vertex is unchanged by an open inclusion, so the
actual selector maps commute with presheaf restriction. -/
theorem selectorCochainEnd_restrict {U V : Opens X} (r : U ⟶ V)
    (φ : Cochains V A n) :
    selectorCochainEnd X A n sel i U ((cochainPresheaf X A n).map r.op φ) =
      (cochainPresheaf X A n).map r.op (selectorCochainEnd X A n sel i V φ) := by
  apply cochain_ext U A n
  intro σ
  rw [selectorCochainEnd_simplex, cochainPresheaf_map_simplex,
    cochainPresheaf_map_simplex]
  exact (selectorCochainEnd_simplex X A n sel i V φ
    (((Opens.toTopCat X).map r).hom.comp σ)).symm

/-- The selector acts on the genuine degreewise singular cochain
presheaf by the original simplex-basis formula. -/
def selectorPresheafEnd : cochainPresheaf X A n ⟶ cochainPresheaf X A n where
  app U := AddCommGrpCat.ofHom (selectorCochainEnd X A n sel i U.unop)
  naturality U V r := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    exact selectorCochainEnd_restrict X A n sel i r.unop φ

open Classical in
/-- Evaluation of the actual presheaf endomorphism on an original
singular simplex. -/
@[simp] theorem selectorPresheafEnd_app_simplex (U : Opens X) (φ : Cochains U A n)
    (σ : SingularSimplex U n) :
    (selectorPresheafEnd X A n sel i).app (op U) φ (simplexChain U n σ) =
      if sel (σ (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1)))).val = i then
        φ (simplexChain U n σ) else 0 :=
  selectorCochainEnd_simplex X A n sel i U φ σ

/-- Every simplex belongs to exactly one selector value. -/
theorem selectorCochainEnd_sum [Fintype ι] (U : Opens X) :
    ∑ i, selectorCochainEnd X A n sel i U = AddMonoidHom.id (Cochains U A n) := by
  classical
  apply AddMonoidHom.ext
  intro φ
  apply cochain_ext U A n
  intro σ
  simp only [AddMonoidHom.finsetSum_apply, selectorCochainEnd_simplex,
    AddMonoidHom.id_apply]
  simp

/-- For a finite selector range, the genuine presheaf endomorphisms
sum to the identity natural transformation. -/
theorem selectorPresheafEnd_sum [Fintype ι] :
    ∑ i, selectorPresheafEnd X A n sel i = 𝟙 (cochainPresheaf X A n) := by
  apply NatTrans.ext
  funext U
  rw [NatTrans.app_sum]
  apply AddCommGrpCat.homAddEquiv.injective
  rw [map_sum]
  exact selectorCochainEnd_sum X A n sel U.unop

/-- An open set with no point assigned to `i` has zero selector map
on its original cochain group. -/
theorem selectorCochainEnd_eq_zero (U : Opens X)
    (h : ∀ x ∈ U, sel x ≠ i) : selectorCochainEnd X A n sel i U = 0 := by
  classical
  apply AddMonoidHom.ext
  intro φ
  apply cochain_ext U A n
  intro σ
  rw [selectorCochainEnd_simplex, if_neg (h _ (σ _).property)]
  rfl

/-- Local vanishing of the actual presheaf endomorphism, without any
assumption about coefficient divisibility or scalar multiplication. -/
theorem selectorPresheafEnd_app_eq_zero (U : Opens X)
    (h : ∀ x ∈ U, sel x ≠ i) : (selectorPresheafEnd X A n sel i).app (op U) = 0 := by
  change AddCommGrpCat.ofHom (selectorCochainEnd X A n sel i U) = 0
  rw [selectorCochainEnd_eq_zero X A n sel i U h]
  rfl

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.FineCochains
