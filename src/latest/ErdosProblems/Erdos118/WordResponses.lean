import ErdosProblems.Erdos118.CoordinateModel
import ErdosProblems.Erdos118.RamseyGame

/-! The actual complete literal words are a nonvacuous thin response family.
The two-completion game theorem applies to this family, but it controls only
separated complete words, not the interleavings needed for a full-order copy. -/

namespace Erdos118.WordResponses

open Negative Negative.Exact CoordinateModel Erdos590.Larson

theorem levelWord_prefix_cancel {a b u v : List ℕ}
    (h : levelWord a ++ u <+: levelWord b ++ v) : a = b ∧ u <+: v := by
  obtain ⟨z, hz⟩ := h
  have hz' : a.length :: (a ++ (u ++ z)) = b.length :: (b ++ v) := by
    simpa only [levelWord, List.cons_append, List.append_assoc] using hz
  have hlen := (List.cons.inj hz').1
  have heq := List.append_inj (List.cons.inj hz').2 hlen
  exact ⟨heq.1, ⟨z, heq.2⟩⟩

theorem flatMap_prefix_rigid {s t : G2} (hlen : s.length = t.length)
    (h : s.flatMap levelWord <+: t.flatMap levelWord) : s = t := by
  induction s generalizing t with
  | nil => simpa using hlen.symm
  | cons a s ih =>
    cases t with
    | nil => simp at hlen
    | cons b t =>
      obtain ⟨rfl, htail⟩ := levelWord_prefix_cancel h
      have hst := ih (by simpa using hlen) htail
      exact congrArg (List.cons a) hst

theorem word_prefix_rigid {s t : G2} (h : word s <+: word t) : s = t := by
  have h' : s.length = t.length ∧
      s.flatMap levelWord <+: t.flatMap levelWord := by
    simpa only [word, List.cons_prefix_cons] using h
  exact flatMap_prefix_rigid h'.1 h'.2

def support (s : G) : Finset ℕ := (word s.1).toFinset

theorem support_injective : Function.Injective support := by
  intro s t hst
  have hword : word s.1 = word t.1 := by
    rw [← sort_toFinset_eq_self_of_pairwise s.2,
      ← sort_toFinset_eq_self_of_pairwise t.2]
    exact congrArg (fun x : Finset ℕ ↦ x.sort (· ≤ ·)) hst
  exact Subtype.ext (word_prefix_rigid (hword ▸ List.prefix_rfl))

def family : Set (Finset ℕ) := Set.range support

theorem family_thin : NashWilliams.FinThin family := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hst
  have hp := (pairwise_isPrefix_iff_initSeg s.2 t.2).2 hst
  have heq : s = t := Subtype.ext (word_prefix_rigid hp)
  exact congrArg support heq

theorem family_hits {H : Set ℕ} (hH : H.Infinite) :
    ∃ s ∈ family, (↑s : Set ℕ) ⊆ H := by
  let x := CoordinateModel.normalized (enumOf_strictMono hH) []
  refine ⟨support x, ⟨x, rfl⟩, ?_⟩
  intro n hn
  have hword : n ∈ word x.1 := List.mem_toFinset.mp hn
  obtain ⟨i, rfl⟩ := CoordinateModel.normalize_supported (enumOf_strictMono hH) [] n hword
  exact enumOf_mem hH i

def responseFamily : RamseyGame.ResponseFamily where
  members := family
  thin := family_thin
  hits := fun _ hH ↦ family_hits hH

noncomputable def supportEquiv : G ≃ family :=
  Equiv.ofInjective support support_injective

@[simp] theorem supportEquiv_apply (s : G) : (supportEquiv s).1 = support s := rfl

@[simp] theorem support_symm (s : family) : support (supportEquiv.symm s) = s.1 := by
  exact congrArg Subtype.val (supportEquiv.apply_symm_apply s)

theorem supported_iff (s : G) (H : Set ℕ) :
    s ∈ Supported H ↔ (↑(support s) : Set ℕ) ⊆ H := by
  simp [Supported, support, Set.subset_def]

theorem red_completion_thinning (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ ∃ b₀ : ℕ,
      ∀ s : G, s ∈ Supported H → (∀ n ∈ word s.1, b₀ < n) →
      ∃ b : ℕ, ∀ t : G, t ∈ Supported H →
        (∀ n ∈ word t.1, b < n) → ¬ B.Adj s t := by
  let C : SimpleGraph family := B.comap supportEquiv.symm
  have hC : C.CliqueFree 3 := cliqueFree_comap B hB supportEquiv.symm.toEmbedding
  obtain ⟨H, hHN, hH, b₀, hred⟩ :=
    RamseyGame.pairGame_red_thinning responseFamily C hC hN
  refine ⟨H, hHN, hH, b₀, ?_⟩
  intro s hs hsbound
  have hsH : (↑(supportEquiv s).1 : Set ℕ) ⊆ H := (supported_iff s H).1 hs
  have hsbound' : ∀ n ∈ (supportEquiv s).1, b₀ < n := by
    simpa only [supportEquiv_apply, support, List.mem_toFinset] using hsbound
  obtain ⟨b, hb⟩ := hred (supportEquiv s) hsH hsbound'
  refine ⟨b, ?_⟩
  intro t ht htbound
  have htH : (↑(supportEquiv t).1 : Set ℕ) ⊆ H := (supported_iff t H).1 ht
  have htbound' : ∀ n ∈ (supportEquiv t).1, b < n := by
    simpa only [supportEquiv_apply, support, List.mem_toFinset] using htbound
  have hout := hb (supportEquiv t) htH htbound'
  simpa only [C, SimpleGraph.comap_adj, supportEquiv.symm_apply_apply] using hout

end Erdos118.WordResponses
