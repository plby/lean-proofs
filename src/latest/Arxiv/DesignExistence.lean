import Arxiv.Arxiv2411_18291.PaperDesignExistence

/-! # A finite-set statement of design existence for Comparator

This exposes Theorem 1.1 of Peter Keevash, *A short proof of the existence of
designs*, arXiv:2411.18291, at its original explicit threshold. The statement
uses only finite sets and numerical divisibility, independently of the
formalization's hypergraph and integral-decomposition definitions.
-/

namespace DesignExistence

theorem designs_exist {q r n : ℕ} (hr : 1 ≤ r) (hqr : r < q)
    (hn : (4 * q) ^ (90 * q * (2 * q) ^ r * (6 * q.choose r) ^ 2) ≤ n)
    (hdiv : ∀ i ≤ r, (q - i).choose (r - i) ∣ (n - i).choose (r - i)) :
    ∃ D : Finset (Finset (Fin n)),
      (∀ Q ∈ D, Q.card = q) ∧
      ∀ e : Finset (Fin n), e.card = r → ∃! Q : Finset (Fin n), Q ∈ D ∧ e ⊆ Q := by
  classical
  have hsize : Arxiv2411_18291.paperSizeThreshold q r ≤ n := by
    simpa only [Arxiv2411_18291.paperSizeThreshold, Arxiv2411_18291.paperInverseAlpha,
      Nat.mul_assoc] using hn
  obtain ⟨D, hD⟩ :=
    (Arxiv2411_18291.hasDecomposition_iff_binomial_divisibility_paper_threshold
      hr hqr hsize).mpr hdiv
  refine ⟨D.image Subtype.val, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hQ
    exact Q.property
  · intro e he
    obtain ⟨Q, hQ, hunique⟩ := hD.unique
      (e := ⟨e, he⟩) (Finset.mem_univ _)
    refine ⟨Q.val, ⟨Finset.mem_image.mpr ⟨Q, hQ.1, rfl⟩, hQ.2⟩, ?_⟩
    rintro R ⟨hR, heR⟩
    obtain ⟨R', hR', rfl⟩ := Finset.mem_image.mp hR
    exact congrArg Subtype.val (hunique R' ⟨hR', heR⟩)

end DesignExistence
