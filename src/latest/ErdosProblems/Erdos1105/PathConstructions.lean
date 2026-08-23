import ErdosProblems.Erdos1105.Basic

namespace Erdos1105

open SimpleGraph

def pathEdge {k : ℕ} (i : Fin k) : (pathGraph (k + 1)).edgeSet :=
  ⟨s(i.castSucc, i.succ), by simp [SimpleGraph.mem_edgeSet, pathGraph_adj]⟩

lemma pathEdge_injective (k : ℕ) : Function.Injective (@pathEdge k) := by
  intro i j hij
  have h : s(i.castSucc, i.succ) = s(j.castSucc, j.succ) := congrArg Subtype.val hij
  simp only [Sym2.eq_iff] at h
  rcases h with ⟨h, _⟩ | ⟨h₁, h₂⟩
  · exact Fin.ext (congrArg (Fin.val (n := k + 1)) h)
  · have h₁' := congrArg Fin.val h₁
    have h₂' := congrArg Fin.val h₂
    simp only [Fin.val_castSucc, Fin.val_succ] at h₁' h₂'
    omega

/-- A rainbow path uses at most two edges at each distinguished vertex,
and at most one edge of each color on the other edges. -/
lemma rainbow_path_length_le {V A : Type*} {ε k : ℕ}
    (S : Finset V) (c : (⊤ : SimpleGraph V).edgeSet → A ⊕ Fin ε)
    (houtside : ∀ a b (hab : a ≠ b), a ∉ S → b ∉ S →
      ∃ i, c ⟨s(a, b), hab⟩ = Sum.inr i)
    (f : (pathGraph (k + 1)).Copy (⊤ : SimpleGraph V))
    (hf : IsRainbow f c) : k ≤ 2 * S.card + ε := by
  classical
  have hne (i : Fin k) : f i.castSucc ≠ f i.succ :=
    f.injective.ne (by intro h; have := congrArg Fin.val h; simp at this)
  have hright (i : Fin k) (ha : f i.castSucc ∉ S) (hb : f i.succ ∉ S) :
      ∃ j, c (f.mapEdgeSet (pathEdge i)) = Sum.inr j :=
    houtside _ _ (hne i) ha hb
  let g : Fin k → (S ⊕ S) ⊕ Fin ε := fun i ↦
    if ha : f i.castSucc ∈ S then Sum.inl (Sum.inl ⟨f i.castSucc, ha⟩)
    else if hb : f i.succ ∈ S then Sum.inl (Sum.inr ⟨f i.succ, hb⟩)
    else Sum.inr (hright i ha hb).choose
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    split_ifs at hij
    all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, Subtype.mk.injEq] at hij
    · exact Fin.ext (congrArg (Fin.val (n := k + 1)) (f.injective hij))
    · have h := congrArg Fin.val (f.injective hij)
      simp only [Fin.val_succ] at h
      exact Fin.ext (by omega)
    · apply pathEdge_injective k
      apply hf
      have hi₁ : f i.castSucc ∉ S := by assumption
      have hi₂ : f i.succ ∉ S := by assumption
      have hj₁ : f j.castSucc ∉ S := by assumption
      have hj₂ : f j.succ ∉ S := by assumption
      exact ((hright i hi₁ hi₂).choose_spec.trans (congrArg Sum.inr hij)).trans
        (hright j hj₁ hj₂).choose_spec.symm
  have hcard := Fintype.card_le_of_injective g hg
  simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_coe] at hcard
  omega

/-- Every edge meeting the first summand gets its own color. The edges in
the second summand retain an arbitrary auxiliary coloring. -/
def hubColoring {A B C : Type*}
    (d : (⊤ : SimpleGraph B).edgeSet → C) :
    (⊤ : SimpleGraph (A ⊕ B)).edgeSet →
      ((⊤ : SimpleGraph A).edgeSet ⊕ (A × B)) ⊕ C :=
  EdgeLabeling.mk (G := ⊤) (fun a b hab ↦ match a, b with
    | Sum.inl x, Sum.inl y =>
      Sum.inl (Sum.inl ⟨s(x, y), fun h ↦ hab (congrArg Sum.inl h)⟩)
    | Sum.inl x, Sum.inr y => Sum.inl (Sum.inr (x, y))
    | Sum.inr x, Sum.inl y => Sum.inl (Sum.inr (y, x))
    | Sum.inr x, Sum.inr y =>
      Sum.inr (d ⟨s(x, y), fun h ↦ hab (congrArg Sum.inr h)⟩)) (by
    intro a b hab
    cases a <;> cases b <;> dsimp
    · congr 2
      exact Subtype.ext Sym2.eq_swap
    · congr 2
      exact Subtype.ext Sym2.eq_swap)

lemma hubColoring_surjective {A B C : Type*}
    (d : (⊤ : SimpleGraph B).edgeSet → C) (hd : Function.Surjective d) :
    Function.Surjective (hubColoring (A := A) d) := by
  intro col
  rcases col with (e | ⟨a, b⟩) | i
  · obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | _ a b =>
      refine ⟨⟨s(Sum.inl a, Sum.inl b), fun h ↦ he (Sum.inl.inj h)⟩, rfl⟩
  · exact ⟨⟨s(Sum.inl a, Sum.inr b), by simp⟩, rfl⟩
  · obtain ⟨⟨e, he⟩, rfl⟩ := hd i
    induction e using Sym2.inductionOn with
    | _ a b =>
      refine ⟨⟨s(Sum.inr a, Sum.inr b), fun h ↦ he (Sum.inr.inj h)⟩, rfl⟩

lemma hubColoring_no_rainbow_path {t r ε k : ℕ}
    (d : (⊤ : SimpleGraph (Fin r)).edgeSet → Fin ε) (hk : 2 * t + ε < k) :
    ∀ f : (pathGraph (k + 1)).Copy (⊤ : SimpleGraph (Fin t ⊕ Fin r)),
      ¬IsRainbow f (hubColoring d) := by
  classical
  let S : Finset (Fin t ⊕ Fin r) := Finset.univ.map Function.Embedding.inl
  have hcard : S.card = t := by simp [S]
  have houtside : ∀ a b : Fin t ⊕ Fin r, ∀ hab : a ≠ b,
      a ∉ S → b ∉ S → ∃ i, hubColoring d ⟨s(a, b), hab⟩ = Sum.inr i := by
    intro a b hab ha hb
    cases a with
    | inl a => simp [S] at ha
    | inr a =>
      cases b with
      | inl b => simp [S] at hb
      | inr b => exact ⟨d ⟨s(a, b), fun h ↦ hab (congrArg Sum.inr h)⟩, rfl⟩
  intro f hf
  have h := rainbow_path_length_le S (hubColoring d) houtside f hf
  rw [hcard] at h
  omega

theorem hub_lower_bound {t r ε k : ℕ}
    (d : (⊤ : SimpleGraph (Fin r)).edgeSet → Fin ε) (hd : Function.Surjective d)
    (hk : 2 * t + ε < k) :
    t.choose 2 + t * r + ε ≤ antiRamseyNum (pathGraph (k + 1)) (t + r) := by
  have h := card_le_antiRamseyNum (hubColoring (A := Fin t) d)
    (hubColoring_surjective d hd) (hubColoring_no_rainbow_path d hk)
  rw [Fintype.card_sum, Fintype.card_sum, card_edgeSet,
    card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  exact h

lemma exists_surjective_edge_coloring {r ε : ℕ} (hε : 0 < ε) (hle : ε ≤ r.choose 2) :
    ∃ d : (⊤ : SimpleGraph (Fin r)).edgeSet → Fin ε, Function.Surjective d := by
  classical
  apply Function.exists_surjective_iff.mpr
  refine ⟨⟨fun _ ↦ ⟨0, hε⟩⟩, Function.Embedding.nonempty_of_card_le ?_⟩
  rwa [Fintype.card_fin, card_edgeSet, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin]

/-- The linear term in the exact path formula is attained by the hub construction. -/
theorem path_linear_lower_bound (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    (ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε ≤
      antiRamseyNum (pathGraph k) n := by
  classical
  dsimp only
  let ℓ := (k - 1) / 2
  let ε := if Odd k then 1 else 2
  have hepos : 0 < ε := by dsimp [ε]; split_ifs <;> omega
  have hele : ε ≤ 2 := by dsimp [ε]; split_ifs <;> omega
  have hr : 3 ≤ n - ℓ + 1 := by dsimp [ℓ]; omega
  have hchoose : ε ≤ (n - ℓ + 1).choose 2 := by
    have h := Nat.choose_le_choose 2 hr
    norm_num at h
    omega
  obtain ⟨d, hd⟩ := exists_surjective_edge_coloring hepos hchoose
  have hlen : 2 * (ℓ - 1) + ε < k - 1 := by
    dsimp [ℓ, ε]
    split_ifs with ho
    · rw [Nat.odd_iff] at ho
      omega
    · rw [Nat.odd_iff] at ho
      omega
  have h := hub_lower_bound (t := ℓ - 1) (k := k - 1) d hd hlen
  have hsum : ℓ - 1 + (n - ℓ + 1) = n := by dsimp [ℓ]; omega
  have hpred : k - 1 + 1 = k := by omega
  rw [hpred, hsum] at h
  exact h

/-- Internal edges of a path on a prescribed set of vertices form a forest,
so at most `|S| - 1` of its edges can lie in a nonempty set `S`. -/
lemma rainbow_path_length_le_clique {V C : Type*} {k : ℕ} (hk : 1 < k)
    (S : Finset V) (c : (⊤ : SimpleGraph V).edgeSet → C) (c₀ : C)
    (houtside : ∀ a b (hab : a ≠ b), a ∉ S ∨ b ∉ S → c ⟨s(a, b), hab⟩ = c₀)
    (f : (pathGraph (k + 1)).Copy (⊤ : SimpleGraph V)) (hf : IsRainbow f c) :
    k ≤ S.card := by
  classical
  let T : Finset (Fin (k + 1)) := Finset.univ.filter (fun v ↦ f v ∈ S)
  let I : Finset (Fin k) := Finset.univ.filter
    (fun i ↦ f i.castSucc ∈ S ∧ f i.succ ∈ S)
  have hTcard : T.card ≤ S.card := Finset.card_le_card_of_injOn f
    (by intro v hv; simpa [T] using hv) f.injective.injOn
  have hout (i : Fin k) (hi : i ∉ I) : c (f.mapEdgeSet (pathEdge i)) = c₀ := by
    have hne : f i.castSucc ≠ f i.succ :=
      f.injective.ne (by intro h; have := congrArg Fin.val h; simp at this)
    apply houtside _ _ hne
    have hi' : ¬ (f i.castSucc ∈ S ∧ f i.succ ∈ S) := by
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    exact not_and_or.mp hi'
  have houtcard : (Finset.univ \ I).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact pathEdge_injective k (hf ((hout i (Finset.mem_sdiff.mp hi).2).trans
      (hout j (Finset.mem_sdiff.mp hj).2).symm))
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hTnonempty : T.Nonempty := by
    by_contra hempty
    have hI : I = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hmem : i.castSucc ∈ T := by
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simpa [T] using hi.1
      exact hempty ⟨_, hmem⟩
    simp only [hI, Finset.sdiff_empty, Finset.card_univ, Fintype.card_fin] at houtcard
    omega
  let v := T.min' hTnonempty
  have hv : v ∈ T := T.min'_mem hTnonempty
  have hIcard : I.card ≤ (T.erase v).card := by
    apply Finset.card_le_card_of_injOn (fun i : Fin k ↦ i.succ) _
      (fun _ _ _ _ h ↦ Fin.ext (by have := congrArg Fin.val h; simp_all))
    intro i hi
    change i ∈ I at hi
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, by simpa [T] using hi.2⟩
    intro he
    have hmin : v ≤ i.castSucc := T.min'_le i.castSucc (by simpa [T] using hi.1)
    have hval := Fin.le_iff_val_le_val.mp hmin
    have heval := congrArg Fin.val he
    simp only [Fin.val_succ, Fin.val_castSucc] at heval hval
    omega
  rw [Finset.card_erase_of_mem hv] at hIcard
  omega

/-- A uniquely colored clique, with one common color on all other edges. -/
def cliqueColoring {A B : Type*} :
    (⊤ : SimpleGraph (A ⊕ B)).edgeSet → Option (⊤ : SimpleGraph A).edgeSet :=
  EdgeLabeling.mk (G := ⊤) (fun a b hab ↦ match a, b with
    | Sum.inl x, Sum.inl y => some ⟨s(x, y), fun h ↦ hab (congrArg Sum.inl h)⟩
    | _, _ => none) (by
    intro a b hab
    cases a <;> cases b <;> dsimp
    congr 1
    exact Subtype.ext Sym2.eq_swap)

lemma cliqueColoring_surjective {t r : ℕ} (ht : 0 < t) (hr : 0 < r) :
    Function.Surjective (cliqueColoring (A := Fin t) (B := Fin r)) := by
  intro c
  cases c with
  | none => exact ⟨⟨s(Sum.inl ⟨0, ht⟩, Sum.inr ⟨0, hr⟩), by simp⟩, rfl⟩
  | some e =>
    obtain ⟨e, he⟩ := e
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨⟨s(Sum.inl a, Sum.inl b), fun h ↦ he (Sum.inl.inj h)⟩, rfl⟩

lemma cliqueColoring_no_rainbow_path (t r k : ℕ) (hk : 1 < k) (ht : t < k) :
    ∀ f : (pathGraph (k + 1)).Copy (⊤ : SimpleGraph (Fin t ⊕ Fin r)),
      ¬IsRainbow f cliqueColoring := by
  classical
  let S : Finset (Fin t ⊕ Fin r) := Finset.univ.map Function.Embedding.inl
  have hcard : S.card = t := by simp [S]
  have hout : ∀ a b : Fin t ⊕ Fin r, ∀ hab : a ≠ b,
      a ∉ S ∨ b ∉ S → cliqueColoring ⟨s(a, b), hab⟩ = none := by
    intro a b hab h
    cases a <;> cases b
    · simp [S] at h
    all_goals rfl
  intro f hf
  have h := rainbow_path_length_le_clique hk S cliqueColoring none hout f hf
  rw [hcard] at h
  omega

/-- The clique term in the exact path formula. -/
theorem path_clique_lower_bound (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    (k - 2).choose 2 + 1 ≤ antiRamseyNum (pathGraph k) n := by
  have h := card_le_antiRamseyNum
    (cliqueColoring (A := Fin (k - 2)) (B := Fin (n - (k - 2))))
    (cliqueColoring_surjective (by omega) (by omega))
    (cliqueColoring_no_rainbow_path (k - 2) (n - (k - 2)) (k - 1) (by omega) (by omega))
  rw [Fintype.card_option, card_edgeSet, card_edgeFinset_top_eq_card_choose_two,
    Fintype.card_fin, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  have hpred : k - 1 + 1 = k := by omega
  have hsum : k - 2 + (n - (k - 2)) = n := by omega
  rwa [hpred, hsum] at h

/-- Both constructions in the proposed exact formula are valid lower bounds. -/
theorem path_formula_lower_bound (k n : ℕ) (hk : 5 ≤ k) (hn : k ≤ n) :
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    max ((k - 2).choose 2 + 1)
      ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε) ≤
      antiRamseyNum (pathGraph k) n :=
  max_le (path_clique_lower_bound k n hk hn) (path_linear_lower_bound k n hk hn)

end Erdos1105
