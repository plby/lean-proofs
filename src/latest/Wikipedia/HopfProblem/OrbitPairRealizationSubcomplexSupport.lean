import Wikipedia.HopfProblem.OrbitPairRealizationMonomorphism

/-!
# Supporting faces of points in a realized subcomplex

If a realized point belongs to a native subcomplex, its unique normal
simplex belongs to that subcomplex. The simplicial degeneracy equation
then shows that the whole positive supporting face belongs as well.
-/

noncomputable section

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.RealizationSimplex

open FirstHurewicz

variable {S : SSet} (A : S.Subcomplex)

def InSubcomplex (p : Parameters S) : Prop := p.1.2 ∈ A.obj (Opposite.op ⦋p.1.1⦌)

theorem mapParameters_inSubcomplex (p : Parameters A.toSSet) :
    InSubcomplex A (mapParameters A.ι p) := p.1.2.property

theorem normalParameters_inSubcomplex_of_mem_range (z : SSet.toTop.obj S)
    (hz : z ∈ Set.range (SSet.toTop.map A.ι)) :
    InSubcomplex A (normalParameters S z) := by
  obtain ⟨u, rfl⟩ := hz
  rw [normalParameters_realizedMap A.ι]
  exact mapParameters_inSubcomplex A _

theorem simplex_mem_of_coreParameters (n : ℕ) (x : S _⦋n⦌) (t : Simplex n)
    (h : InSubcomplex A (coreParameters S n x t)) : x ∈ A.obj (Opposite.op ⦋n⦌) := by
  let c := core S n x
  have hc : c.simplex.val ∈ A.obj (Opposite.op ⦋c.dim⦌) := h
  have hm : S.map c.collapse.op c.simplex.val ∈ A.obj (Opposite.op ⦋n⦌) :=
    A.map c.collapse.op hc
  exact c.decomposes.symm ▸ hm

theorem support_simplex_mem (n : ℕ) (x : S _⦋n⦌) (t : Simplex n)
    (a : SimplexSupport.Face n t)
    (hz : characteristic S n x t ∈ Set.range (SSet.toTop.map A.ι)) :
    S.map a.inclusion.op x ∈ A.obj (Opposite.op ⦋a.dim⦌) := by
  have hn : normalParameters S (characteristic S n x t) =
      coreParameters S a.dim (S.map a.inclusion.op x) a.point :=
    (normalize_eq_normalParameters S ⟨⟨n, x⟩, t⟩).symm.trans (normalize_eq_face S n x t a)
  have hm := normalParameters_inSubcomplex_of_mem_range A (characteristic S n x t) hz
  rw [hn] at hm
  exact simplex_mem_of_coreParameters A a.dim (S.map a.inclusion.op x) a.point hm

theorem subcomplex_support_characteristic (n : ℕ) (x : S _⦋n⦌) (t : Simplex n)
    (a : SimplexSupport.Face n t)
    (ha : S.map a.inclusion.op x ∈ A.obj (Opposite.op ⦋a.dim⦌)) :
    (SSet.toTop.map A.ι) (characteristic A.toSSet a.dim ⟨S.map a.inclusion.op x, ha⟩ a.point) =
      characteristic S n x t := by
  have hc := congrArg (fun f : C(Simplex a.dim, SSet.toTop.obj S) ↦ f a.point)
    (characteristic_map S a.dim n a.inclusion x)
  exact (realizedMap_characteristic A.ι a.dim ⟨S.map a.inclusion.op x, ha⟩ a.point).trans
    (hc.trans (congrArg (characteristic S n x) a.map_point))

end Wikipedia.HopfProblem.OrbitPair.RealizationSimplex
