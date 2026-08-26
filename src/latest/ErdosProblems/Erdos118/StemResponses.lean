import ErdosProblems.Erdos118.RootResponses

/-!
Exact responses that finish an interior body and fill to a prescribed body
count, including final completion. Labels on new filler bodies are empty.
Thinness follows from literal markers and the fixed final label list.
-/

namespace Erdos118.StemResponses

open LabelledExtensions Negative Negative.Exact Erdos590.Larson

structure Setup (P : Position) (j : ℕ) where
  stem : Stem
  newWord : List ℕ
  root_eq : stem.root = P.stem.root
  rootLabel_eq : stem.rootLabel = P.stem.rootLabel
  count : stem.done.length = j
  labels : stem.bodyLabels = P.bodyLabels ++ List.replicate (j - (P.stem.done.length + 1)) []
  decorated : stem.decorated = P.decorated ++ newWord
  ordinary : stem.ordinary = P.ordinary ++ newWord
  nonempty : newWord ≠ []

theorem bodies_eq_of_projections {p q : List Body}
    (hv : p.map Body.values = q.map Body.values)
    (hl : p.map Body.label = q.map Body.label) : p = q := by
  induction p generalizing q with
  | nil => simpa using hv.symm
  | cons a p ih =>
    cases q with
    | nil => simp at hv
    | cons b q =>
      obtain ⟨hav, hpv⟩ := List.cons.inj hv
      obtain ⟨hal, hpl⟩ := List.cons.inj hl
      have hab : a = b := by
        cases a
        cases b
        cases hav
        cases hal
        rfl
      exact congrArg₂ List.cons hab (ih hpv hpl)

theorem newWord_pairwise {P : Position} {j : ℕ} (A : Setup P j) :
    A.newWord.Pairwise (· < ·) := by
  have h : (P.decorated ++ A.newWord).Pairwise (· < ·) := A.decorated ▸ A.stem.increasing
  exact (List.pairwise_append.mp h).2.1

theorem setup_eq_of_prefix {P : Position} {j : ℕ} (A B : Setup P j)
    (h : A.newWord <+: B.newWord) : A = B := by
  have hord : A.stem.ordinary <+: B.stem.ordinary := by
    rw [A.ordinary, B.ordinary, List.prefix_append_right_inj]
    exact h
  have hflat : A.stem.done.flatMap Body.ordinary <+: B.stem.done.flatMap Body.ordinary := by
    simpa only [Stem.ordinary, A.root_eq, B.root_eq, List.cons_prefix_cons, true_and] using hord
  have hvalues : A.stem.done.map Body.values = B.stem.done.map Body.values := by
    apply WordResponses.flatMap_prefix_rigid
    · simp only [List.length_map, A.count, B.count]
    · simp only [List.flatMap_map]
      exact hflat
  have hlabels : A.stem.done.map Body.label = B.stem.done.map Body.label :=
    A.labels.trans B.labels.symm
  have hdone := bodies_eq_of_projections hvalues hlabels
  have stem_ext : ∀ s t : Stem, s.root = t.root → s.rootLabel = t.rootLabel →
      s.done = t.done → s = t := by
    intro s t
    cases s
    cases t
    intro hr hl hd
    cases hr
    cases hl
    cases hd
    rfl
  have hstem := stem_ext A.stem B.stem (A.root_eq.trans B.root_eq.symm)
    (A.rootLabel_eq.trans B.rootLabel_eq.symm) hdone
  have hword : A.newWord = B.newWord := by
    apply List.append_cancel_left (as := P.ordinary)
    rw [← A.ordinary, ← B.ordinary, hstem]
  cases A with
  | mk a v _ _ _ _ _ _ _ =>
    cases B with
    | mk b w _ _ _ _ _ _ _ =>
      change a = b at hstem
      change v = w at hword
      cases hstem
      cases hword
      rfl

def support {P : Position} {j : ℕ} (A : Setup P j) : Finset ℕ := A.newWord.toFinset

theorem support_injective (P : Position) (j : ℕ) :
    Function.Injective (support (P := P) (j := j)) := by
  intro A B hAB
  have hw : A.newWord = B.newWord := by
    rw [← sort_toFinset_eq_self_of_pairwise (newWord_pairwise A),
      ← sort_toFinset_eq_self_of_pairwise (newWord_pairwise B)]
    exact congrArg (fun s : Finset ℕ ↦ s.sort (· ≤ ·)) hAB
  exact setup_eq_of_prefix A B (hw ▸ List.prefix_rfl)

def family (P : Position) (j : ℕ) : Set (Finset ℕ) :=
  Set.range (support (P := P) (j := j))

theorem family_thin (P : Position) (j : ℕ) : NashWilliams.FinThin (family P j) := by
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩ hAB
  have hp := (pairwise_isPrefix_iff_initSeg (newWord_pairwise A) (newWord_pairwise B)).2 hAB
  exact congrArg support (setup_eq_of_prefix A B hp)

theorem setup_above (P : Position) (j : ℕ) (hpj : P.stem.done.length < j)
    (hjm : j ≤ P.stem.root) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ A : Setup P j, ∀ x ∈ A.newWord, x ∈ H ∧ b < x := by
  obtain ⟨S, u, hr, hC, hlen, _, hlabels, hdec, hord, hune, hu⟩ := finish_body P hH b
  have hij : S.done.length ≤ j := by rw [hlen]; omega
  obtain ⟨T, v, hrT, hCT, hlenT, _, hdecT, hordT, hv, p, hdoneT⟩ :=
    fill_stem_plain S hH b j hij (hr.symm ▸ hjm)
  have hlabelsS : S.bodyLabels = P.bodyLabels := by
    apply (List.IsPrefix.eq_of_length hlabels ?_).symm
    simp only [Position.bodyLabels, Stem.bodyLabels, List.length_append, List.length_map,
      List.length_singleton, hlen]
  have hplen : p.length = j - (P.stem.done.length + 1) := by
    have he := congrArg List.length hdoneT
    simp only [List.length_append, List.length_map, hlenT, hlen] at he
    omega
  have hlabelsT : T.bodyLabels =
      P.bodyLabels ++ List.replicate (j - (P.stem.done.length + 1)) [] := by
    change T.done.map Body.label = _
    rw [hdoneT, List.map_append, List.map_map]
    change S.bodyLabels ++ p.map (fun _ ↦ []) = _
    rw [hlabelsS, List.map_const', hplen]
  let A : Setup P j :=
    { stem := T, newWord := u ++ v
      root_eq := hrT.trans hr
      rootLabel_eq := hCT.trans hC
      count := hlenT
      labels := hlabelsT
      decorated := by rw [hdecT, hdec, List.append_assoc]
      ordinary := by rw [hordT, hord, List.append_assoc]
      nonempty := by intro he; exact hune (List.append_eq_nil_iff.mp he).1 }
  refine ⟨A, ?_⟩
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hu x hx
  · exact hv x hx

theorem family_hits (P : Position) (j : ℕ) (hpj : P.stem.done.length < j)
    (hjm : j ≤ P.stem.root) {H : Set ℕ} (hH : H.Infinite) :
    ∃ a ∈ family P j, (↑a : Set ℕ) ⊆ H := by
  obtain ⟨A, hA⟩ := setup_above P j hpj hjm hH 0
  exact ⟨support A, ⟨A, rfl⟩, fun x hx ↦ (hA x (List.mem_toFinset.mp hx)).1⟩

def responseFamily (P : Position) (j : ℕ) (hpj : P.stem.done.length < j)
    (hjm : j ≤ P.stem.root) : RamseyGame.ResponseFamily where
  members := family P j
  thin := family_thin P j
  hits := fun _ hH ↦ family_hits P j hpj hjm hH

noncomputable def supportEquiv (P : Position) (j : ℕ) : Setup P j ≃ family P j :=
  Equiv.ofInjective support (support_injective P j)

@[simp] theorem supportEquiv_apply {P : Position} {j : ℕ} (A : Setup P j) :
    (supportEquiv P j A).1 = support A := rfl

@[simp] theorem support_symm {P : Position} {j : ℕ} (a : family P j) :
    support ((supportEquiv P j).symm a) = a.1 :=
  congrArg Subtype.val ((supportEquiv P j).apply_symm_apply a)

theorem labels_prefix {P : Position} {j : ℕ} (A : Setup P j) :
    P.bodyLabels <+: A.stem.bodyLabels := by
  rw [A.labels]
  exact List.prefix_append _ _

def completed {P : Position} (A : Setup P P.stem.root) : G :=
  A.stem.toGood (A.count.trans A.root_eq.symm)

theorem completed_word {P : Position} (A : Setup P P.stem.root) :
    word (completed A).1 = P.ordinary ++ A.newWord :=
  (A.stem.toGood_word _).trans A.ordinary

end Erdos118.StemResponses
