import Arxiv.Arxiv2411_18291.CliqueCover
import Arxiv.Arxiv2411_18291.AsymptoticPrescribedGreedy

/-!
# Existence of a cover using reserve edges

For `0 < a < 1/2`, a leave of degree scale `n^(-3*a)` can be covered
whenever each of its edges has at least `n^(-a)*n^(q-r)` punctured
cliques in the reserve. The threshold is uniform over the leave and reserve.
This is the eventual form of the paper's Cover lemma; the reserve's own
degree bound is not needed once its clique-extension counts are given.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}

omit [DecidableEq W] in
theorem eventually_exists_indexed_clique_cover (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q) {a : ℝ} (ha : 0 < a) (ha1 : a < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ, ∀ E : ℕ → Block (Fin n) (r + 1),
      ∀ R : Hypergraph (Fin n) (r + 1),
      Function.Injective (fun i : Fin t => E i) → (∀ i < t, E i ∉ R) →
      IsEdgeFamilyBounded (fun i : Fin t => E i) ((n : ℝ) ^ (-(3 * a))) →
      (∀ i < t, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R (E i) q).card) →
      ∃ Q : Fin t → Block (Fin n) q, IsCliqueCover R (fun i : Fin t => E i) Q := by
  classical
  have hba : 2 * a < 3 * a := by linarith
  have hca : a < 3 * a := by linarith
  have hb1 : 3 * a - a < 1 := by linarith
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_exists_greedy_family_in_candidates (complete W (r + 1))
      (complete_root_admissible F₀) hba hca hb1] with n hn hgreedy
  intro t E R hE hER hbound hcount
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  let A : (i : ℕ) → Finset (EmbeddingExtension (Φ i)) :=
    fun i => cliqueCandidateExtensions (Φ i) hW R (E i)
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : IsGraphBounded (∅ : Hypergraph (Fin n) (r + 1)) ((n : ℝ) ^ (-(3 * a))) :=
    isGraphBounded_empty (Real.rpow_pos_of_pos hx _) (by simpa only [Fintype.card_fin] using hn)
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        ((n : ℝ) ^ (-(3 * a))) := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap] using hbound
  have hsize : ∀ i < t, (n : ℝ) ^ (-a) *
      (n : ℝ) ^ (Fintype.card W - F₀.val.card) ≤ (A i).card := by
    intro i hi
    have hc : ((puncturedCliques R (E i) q).card : ℝ) ≤ (A i).card := by
      exact_mod_cast cliqueCandidateExtensions_card_ge (Φ i) hW R (E i)
        (edgeRootMap_usedVertices F₀ (E i))
    simpa only [hW, F₀.property] using (hcount i hi).trans hc
  obtain ⟨Ψ, hΨ, hmem⟩ := hgreedy t Φ A ∅ hB hroots hsize
  exact ⟨fun i => embeddingClique hW (Ψ i).val,
    hΨ.cliqueCover F₀ hW (fun i => E i) R ∅ Ψ hE (fun i => hER i i.isLt) hmem⟩

omit [Fintype W] [DecidableEq W] in
theorem eventually_exists_clique_cover (hq : r + 1 ≤ q) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ R L : Hypergraph (Fin n) (r + 1),
      Disjoint L R → IsGraphBounded L ((n : ℝ) ^ (-(3 * a))) →
      (∀ e ∈ L, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R e q).card) →
      ∃ Q : L → Block (Fin n) q, IsCliqueCover R (fun e => e.val) Q := by
  obtain ⟨s, _, hs⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (by simpa only [card_univ, Fintype.card_fin] using hq)
  let F₀ : Block (Fin q) (r + 1) := ⟨s, hs⟩
  filter_upwards [eventually_exists_indexed_clique_cover F₀ (Fintype.card_fin q) ha ha1]
    with n hcover
  intro R L hLR hL hcount
  rcases L.eq_empty_or_nonempty with hL0 | hLpos
  · subst L
    exact ⟨fun e => (notMem_empty _ e.property).elim,
      ⟨fun e => (notMem_empty _ e.property).elim,
        fun i _ _ => (notMem_empty _ i.property).elim⟩⟩
  · obtain ⟨e₀, _⟩ := hLpos
    let enum : Fin L.card ≃ L := L.equivFin.symm
    let E : ℕ → Block (Fin n) (r + 1) :=
      fun i => if hi : i < L.card then (enum ⟨i, hi⟩).val else e₀
    have hE (i : Fin L.card) : E i = (enum i).val := by
      dsimp [E]
      rw [if_pos i.isLt]
    have hEmem (i : Fin L.card) : E i ∈ L := hE i ▸ (enum i).property
    have hEinj : Function.Injective (fun i : Fin L.card => E i) := by
      intro i j hij
      apply enum.injective
      apply Subtype.ext
      simpa only [hE] using hij
    have hER : ∀ i < L.card, E i ∉ R := by
      intro i hi
      exact fun hR => disjoint_left.mp hLR (hEmem ⟨i, hi⟩) hR
    have hEcount : ∀ i < L.card, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques R (E i) q).card :=
      fun i hi => hcount (E i) (hEmem ⟨i, hi⟩)
    obtain ⟨Q, hQ⟩ := hcover L.card E R hEinj hER
      (hL.edgeFamily (fun i : Fin L.card => E i) hEmem hEinj) hEcount
    refine ⟨fun e => Q (enum.symm e), ?_⟩
    constructor
    · intro e
      have heq : E (enum.symm e) = e.val := by
        rw [hE, Equiv.apply_symm_apply]
      simpa only [heq] using hQ.punctured (enum.symm e)
    · intro e f hef
      exact hQ.disjoint (fun h => hef (enum.symm.injective h))

end Arxiv2411_18291
