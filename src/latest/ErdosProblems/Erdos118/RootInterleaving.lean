import ErdosProblems.Erdos118.PartialWordResponses
import ErdosProblems.Erdos118.SynchronizedRounds

/-!
Inside and outside root-split games on literal good words. Both blue
outcomes force a triangle. These specific interleavings do not yet cover
the multiple interior cuts required for the full positive relation.
-/

namespace Erdos118.RootInterleaving

open Negative Negative.Exact Erdos590.Larson RamseyGame

def singletonFamily : Set (Finset ℕ) := Set.range (fun n : ℕ ↦ ({n} : Finset ℕ))

theorem singletonFamily_thin : NashWilliams.FinThin singletonFamily := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ h
  have hm : m ∈ ({n} : Finset ℕ) := h.1 (Finset.mem_singleton_self m)
  exact congrArg (fun n : ℕ ↦ ({n} : Finset ℕ)) (Finset.mem_singleton.mp hm)

def rootResponse : ResponseFamily where
  members := singletonFamily
  thin := singletonFamily_thin
  hits := by
    intro H hH
    obtain ⟨n, hn⟩ := hH.nonempty
    exact ⟨{n}, ⟨n, rfl⟩, by simpa using hn⟩

noncomputable def rootEquiv : ℕ ≃ singletonFamily :=
  Equiv.ofInjective (fun n : ℕ ↦ ({n} : Finset ℕ))
    (fun _ _ h ↦ Finset.singleton_injective h)

@[simp] theorem rootEquiv_apply (n : ℕ) : (rootEquiv n).1 = {n} := rfl

def completionResponse (m : ℕ) : ResponseFamily where
  members := PartialWordResponses.completionFamily [m]
  thin := PartialWordResponses.completionFamily_thin [m]
  hits := by
    intro H hH
    let f := enumOf H
    have hf : StrictMono f := enumOf_strictMono hH
    let t := CoordinateModel.normalizeTail f m (List.replicate m [])
    have htlen : t.length = m := by simp [t]
    have ht := CoordinateModel.normalizeTail_spec hf m (List.replicate m [])
    have hgood : (word t).Pairwise (· < ·) := by
      rw [word, htlen, List.pairwise_cons]
      exact ⟨ht.1, ht.2.1⟩
    refine ⟨(t.flatMap levelWord).toFinset,
      ⟨⟨t, hgood⟩, t.flatMap levelWord, ?_, rfl⟩, ?_⟩
    · simp only [word, htlen, List.singleton_append]
    · intro z hz
      obtain ⟨i, rfl⟩ := ht.2.2 z (List.mem_toFinset.mp hz)
      exact enumOf_mem hH i

noncomputable def assemble (m : ℕ) (r : (completionResponse m).members) : G :=
  Classical.choose r.2

theorem assemble_word (m : ℕ) (r : (completionResponse m).members) :
    ∃ s : List ℕ, word (assemble m r).1 = [m] ++ s ∧ s.toFinset = r.1 :=
  Classical.choose_spec r.2

theorem assemble_support (m : ℕ) (r : (completionResponse m).members) :
    WordResponses.support (assemble m r) = insert m r.1 := by
  obtain ⟨s, hs, hr⟩ := assemble_word m r
  simp only [WordResponses.support, hs, List.singleton_append, List.toFinset_cons, hr]

/-- Elimination and introduction at a response node preserve all actual bounds. -/
theorem response_outcome_iff (F : ResponseFamily) (next : F.members → Game)
    (H : Set ℕ) (value : Bool) :
    Outcome H (.response F next) value ↔ ∃ b : ℕ,
      ∀ s : F.members, (↑s.1 : Set ℕ) ⊆ H → (∀ n ∈ s.1, b < n) →
        Outcome H (next s) value := by
  constructor
  · intro h
    cases h with
    | response _ _ b _ h => exact ⟨b, h⟩
  · rintro ⟨b, h⟩
    exact .response F next b value h

noncomputable def insideGame (B : SimpleGraph G) : Game := by
  classical
  exact .response rootResponse (fun m ↦
    .response WordResponses.responseFamily (fun t ↦
      .response (completionResponse (rootEquiv.symm m)) (fun r ↦
        .leaf (decide (B.Adj (assemble (rootEquiv.symm m) r)
          (WordResponses.supportEquiv.symm t))))))

noncomputable def outsideGame (B : SimpleGraph G) : Game := by
  classical
  exact .response rootResponse (fun m ↦
    .response rootResponse (fun n ↦
      .response (completionResponse (rootEquiv.symm m)) (fun r ↦
        .response (completionResponse (rootEquiv.symm n)) (fun s ↦
          .leaf (decide (B.Adj (assemble (rootEquiv.symm m) r)
            (assemble (rootEquiv.symm n) s)))))))

/-- The concrete outside game is a two-round instance of the general protocol. -/
noncomputable def rootProtocol : SynchronizedRounds.Protocol G 2 :=
  .response rootResponse (fun m ↦
    .response (completionResponse (rootEquiv.symm m)) (fun r ↦
      .leaf (assemble (rootEquiv.symm m) r)))

theorem rootProtocol_pairGame (B : SimpleGraph G) :
    SynchronizedRounds.pairGame B rootProtocol rootProtocol = outsideGame B := rfl

theorem root_high {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ m : singletonFamily, (↑m.1 : Set ℕ) ⊆ H ∧
      (∀ n ∈ m.1, b < n) ∧ rootEquiv.symm m ∈ H ∧ b < rootEquiv.symm m := by
  obtain ⟨m, hmH, hmb⟩ := rootResponse.conservative_exists hH b
  have hm : m.1 = {rootEquiv.symm m} := by
    have h := congrArg Subtype.val (rootEquiv.apply_symm_apply m)
    exact h.symm
  have hmem : rootEquiv.symm m ∈ m.1 := by rw [hm]; exact Finset.mem_singleton_self _
  exact ⟨m, hmH, hmb, hmH hmem, hmb _ hmem⟩

theorem inside_triangle (B : SimpleGraph G) {H : Set ℕ} (hH : H.Infinite)
    (hwin : Outcome H (insideGame B) true) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  classical
  have edge {s t : G} (h : Outcome H (.leaf (decide (B.Adj s t))) true) :
      B.Adj s t := of_decide_eq_true (outcome_leaf_iff.mp h)
  simp only [insideGame, response_outcome_iff] at hwin
  obtain ⟨b₀, hfirst⟩ := hwin
  obtain ⟨m, hmH, hmb, _, _⟩ := root_high hH b₀
  obtain ⟨bm, hm⟩ := hfirst m hmH hmb
  obtain ⟨n, hnH, hnb, hnvalH, hnvalb⟩ := root_high hH (max b₀ bm)
  obtain ⟨bn, hn⟩ := hfirst n hnH
    (fun z hz ↦ (le_max_left b₀ bm).trans_lt (hnb z hz))
  obtain ⟨u, huH, hub⟩ := WordResponses.responseFamily.conservative_exists hH (max bm bn)
  obtain ⟨bmu, hmu⟩ := hm u huH
    (fun z hz ↦ (le_max_left bm bn).trans_lt (hub z hz))
  obtain ⟨bnu, hnu⟩ := hn u huH
    (fun z hz ↦ (le_max_right bm bn).trans_lt (hub z hz))
  obtain ⟨rn, hrnH, hrnb⟩ :=
    (completionResponse (rootEquiv.symm n)).conservative_exists hH (max bnu bm)
  let t := WordResponses.supportEquiv (assemble (rootEquiv.symm n) rn)
  have htH : (↑t.1 : Set ℕ) ⊆ H := by
    intro z hz
    change z ∈ WordResponses.support (assemble (rootEquiv.symm n) rn) at hz
    rw [assemble_support] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hnvalH
    · exact hrnH hz
  have htb : ∀ z ∈ t.1, bm < z := by
    intro z hz
    change z ∈ WordResponses.support (assemble (rootEquiv.symm n) rn) at hz
    rw [assemble_support] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact (le_max_right b₀ bm).trans_lt hnvalb
    · exact (le_max_right bnu bm).trans_lt (hrnb z hz)
  obtain ⟨bmt, hmt⟩ := hm t htH htb
  obtain ⟨rm, hrmH, hrmb⟩ :=
    (completionResponse (rootEquiv.symm m)).conservative_exists hH (max bmu bmt)
  refine ⟨assemble (rootEquiv.symm m) rm, assemble (rootEquiv.symm n) rn,
    WordResponses.supportEquiv.symm u, ?_, ?_, ?_⟩
  · have h := edge (hmt rm hrmH
      (fun z hz ↦ (le_max_right bmu bmt).trans_lt (hrmb z hz)))
    simpa only [t, Equiv.symm_apply_apply] using h
  · exact edge (hmu rm hrmH
      (fun z hz ↦ (le_max_left bmu bmt).trans_lt (hrmb z hz)))
  · exact edge (hnu rn hrnH
      (fun z hz ↦ (le_max_left bnu bm).trans_lt (hrnb z hz)))

theorem outside_triangle (B : SimpleGraph G) {H : Set ℕ} (hH : H.Infinite)
    (hwin : Outcome H (outsideGame B) true) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  classical
  have edge {s t : G} (h : Outcome H (.leaf (decide (B.Adj s t))) true) :
      B.Adj s t := of_decide_eq_true (outcome_leaf_iff.mp h)
  simp only [outsideGame, response_outcome_iff] at hwin
  obtain ⟨b₀, hfirst⟩ := hwin
  obtain ⟨m, hmH, hmb, _, _⟩ := root_high hH b₀
  obtain ⟨bm, hm⟩ := hfirst m hmH hmb
  obtain ⟨n, hnH, hnb, _, _⟩ := root_high hH (max b₀ bm)
  obtain ⟨bn, hn⟩ := hfirst n hnH
    (fun z hz ↦ (le_max_left b₀ bm).trans_lt (hnb z hz))
  obtain ⟨k, hkH, hkb, _, _⟩ := root_high hH (max bm bn)
  obtain ⟨bmn, hmn⟩ := hm n hnH
    (fun z hz ↦ (le_max_right b₀ bm).trans_lt (hnb z hz))
  obtain ⟨bmk, hmk⟩ := hm k hkH
    (fun z hz ↦ (le_max_left bm bn).trans_lt (hkb z hz))
  obtain ⟨bnk, hnk⟩ := hn k hkH
    (fun z hz ↦ (le_max_right bm bn).trans_lt (hkb z hz))
  obtain ⟨rm, hrmH, hrmb⟩ :=
    (completionResponse (rootEquiv.symm m)).conservative_exists hH (max bmn bmk)
  obtain ⟨cmn, hmnr⟩ := hmn rm hrmH
    (fun z hz ↦ (le_max_left bmn bmk).trans_lt (hrmb z hz))
  obtain ⟨cmk, hmkr⟩ := hmk rm hrmH
    (fun z hz ↦ (le_max_right bmn bmk).trans_lt (hrmb z hz))
  obtain ⟨rn, hrnH, hrnb⟩ :=
    (completionResponse (rootEquiv.symm n)).conservative_exists hH (max cmn bnk)
  obtain ⟨cnk, hnkr⟩ := hnk rn hrnH
    (fun z hz ↦ (le_max_right cmn bnk).trans_lt (hrnb z hz))
  obtain ⟨rk, hrkH, hrkb⟩ :=
    (completionResponse (rootEquiv.symm k)).conservative_exists hH (max cmk cnk)
  refine ⟨assemble (rootEquiv.symm m) rm, assemble (rootEquiv.symm n) rn,
    assemble (rootEquiv.symm k) rk, ?_, ?_, ?_⟩
  · exact edge (hmnr rn hrnH
      (fun z hz ↦ (le_max_left cmn bnk).trans_lt (hrnb z hz)))
  · exact edge (hmkr rk hrkH
      (fun z hz ↦ (le_max_left cmk cnk).trans_lt (hrkb z hz)))
  · exact edge (hnkr rk hrkH
      (fun z hz ↦ (le_max_right cmk cnk).trans_lt (hrkb z hz)))

theorem inside_red_outcome (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ Outcome H (insideGame B) false := by
  obtain ⟨H, hHN, hH, value, hval⟩ := dichotomy (insideGame B) N hN
  cases value with
  | false => exact ⟨H, hHN, hH, hval⟩
  | true =>
    obtain ⟨s, t, u, hst, hsu, htu⟩ := inside_triangle B hH hval
    exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim

theorem outside_red_outcome (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ Outcome H (outsideGame B) false := by
  obtain ⟨H, hHN, hH, value, hval⟩ := dichotomy (outsideGame B) N hN
  cases value with
  | false => exact ⟨H, hHN, hH, hval⟩
  | true =>
    obtain ⟨s, t, u, hst, hsu, htu⟩ := outside_triangle B hH hval
    exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim

theorem both_red_outcomes (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ Outcome H (insideGame B) false ∧
      Outcome H (outsideGame B) false := by
  obtain ⟨K, hKN, hK, hin⟩ := inside_red_outcome B hB hN
  obtain ⟨H, hHK, hH, hout⟩ := outside_red_outcome B hB hK
  exact ⟨H, hHK.trans hKN, hH, hin.almost_mono (almostSubset_of_subset hHK), hout⟩

end Erdos118.RootInterleaving
