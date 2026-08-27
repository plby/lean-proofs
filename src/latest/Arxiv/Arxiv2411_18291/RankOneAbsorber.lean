import Arxiv.Arxiv2411_18291.RankOneDesign
import Arxiv.Arxiv2411_18291.Absorption

/-! # Rank-one leaves need no nonempty absorber -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_rank_one_graph_embedding {V : Type*} [DecidableEq V]
    (J : Hypergraph V 1) : ∃ φ : J ↪ V, mapGraph φ (complete J 1) = J := by
  classical
  have hx (e : J) : ∃ v : V, e.val.val = {v} := card_eq_one.mp e.val.property
  choose f hf using hx
  let φ : J ↪ V := ⟨f, fun i j hij => Subtype.ext (Subtype.ext (by rw [hf i, hf j, hij]))⟩
  refine ⟨φ, ?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨d, _, rfl⟩ := (mem_mapGraph _ _ _).mp he
    obtain ⟨i, hi⟩ := card_eq_one.mp d.property
    have heq : mapBlock φ d = i.val := by
      apply Subtype.ext
      change d.val.map φ = i.val.val
      rw [hi, map_singleton, hf i]
      rfl
    rw [heq]
    exact i.property
  · intro he
    let i : J := ⟨e, he⟩
    refine (mem_mapGraph _ _ _).mpr ⟨⟨{i}, card_singleton i⟩, mem_univ _, ?_⟩
    apply Subtype.ext
    change ({i} : Finset J).map φ = e.val
    rw [map_singleton, show e.val = {f i} from hf i]
    rfl

theorem hasDecomposition_one_of_divisible {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {J : Hypergraph V 1} (hJ : Divisible q J) : HasDecomposition q J := by
  classical
  have hdvd : q ∣ J.card := by
    have h := hJ.degree_dvd ∅ (by simp)
    rw [degree_indicator] at h
    simp only [card_empty, Nat.sub_zero, Nat.choose_one_right, empty_subset,
      filter_true] at h
    exact_mod_cast h
  obtain ⟨φ, hφ⟩ := exists_rank_one_graph_embedding J
  obtain ⟨D, hD⟩ := hasDecomposition_complete_one_of_dvd (V := ↥J)
    (by simpa only [Fintype.card_coe] using hdvd : q ∣ Fintype.card J)
  have hm := hD.map φ
  rw [hφ] at hm
  exact ⟨mapGraph φ D, hm⟩

theorem empty_isAbsorber_one {V : Type*} [Fintype V] [DecidableEq V]
    (q : ℕ) (B : Hypergraph V 1) : IsAbsorber q ∅ B := by
  refine ⟨disjoint_empty_left B, ?_⟩
  intro J _ hJ
  simpa only [empty_union] using hasDecomposition_one_of_divisible hJ

end Arxiv2411_18291
