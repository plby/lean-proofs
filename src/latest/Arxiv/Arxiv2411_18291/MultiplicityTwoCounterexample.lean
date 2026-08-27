import Arxiv.Arxiv2411_18291.MultiplicityTwoObstruction

/-! # Counterexamples to universal integral generation with multiplicity two -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem not_exists_multiplicity_two_integral_generators (hqr : r ≤ q)
    (hk : 2 < q.choose r) (hn : q + r ≤ Fintype.card V)
    (R : Hypergraph V r) (hR : R.Nonempty) :
    ¬∃ D : Finset (Block V q),
      (∀ e : Block V r, (D.filter fun Q => e.val ⊆ Q.val).card ≤ 2) ∧
        ∀ J : Block V r → ℤ, (∀ e, e ∉ R → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  rintro ⟨D, hmult, hgen⟩
  obtain ⟨e, he⟩ := hR
  obtain ⟨Z, heZ, _, hZ⟩ := exists_subsuperset_card_eq (subset_univ e.val)
    (by rw [e.property]; omega : e.val.card ≤ q + r) (by simpa only [card_univ] using hn)
  obtain ⟨Ψ, hΨ, _, _⟩ := local_decoder_on Z hZ hqr e heZ
  have hN : ((r.factorial * q.choose r : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.factorial_pos r) (Nat.choose_pos hqr)).ne'
  apply not_generatedBy_single_edge_of_multiplicity_two D hmult hk e hN
  refine hgen (fun f => if f = e then ((r.factorial * q.choose r : ℕ) : ℤ) else 0) ?_
    ⟨Ψ, hΨ⟩
  intro f hf
  apply if_neg
  intro hfe
  exact hf (hfe.symm ▸ he)

theorem local_cliques_not_flattenable_to_two (hqr : r ≤ q) (hk : 2 < q.choose r)
    (Z : Block V (q + r)) (e : Block V r) (heZ : e.val ⊆ Z.val) :
    ¬∃ F : Finset (Block V q),
      (∀ f : Block V r, (F.filter fun Q => f.val ⊆ Q.val).card ≤ 2) ∧
        ∀ J : Block V r → ℤ, GeneratedBy (cliqueEdges q Z) J → GeneratedBy F J := by
  rintro ⟨F, hmult, hgen⟩
  obtain ⟨Ψ, hΨ, hsupport, _⟩ := local_decoder_on Z.val Z.property hqr e heZ
  have hN : ((r.factorial * q.choose r : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.factorial_pos r) (Nat.choose_pos hqr)).ne'
  apply not_generatedBy_single_edge_of_multiplicity_two F hmult hk e hN
  apply hgen _
  refine ⟨Ψ, hΨ, ?_⟩
  intro Q hQ
  exact hsupport Q (fun hQZ => hQ ((mem_cliqueEdges Q Z).mpr hQZ))

end Arxiv2411_18291
