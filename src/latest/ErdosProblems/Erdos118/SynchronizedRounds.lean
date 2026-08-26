import ErdosProblems.Erdos118.RamseyGame

/-!
Triangle synchronization for a fixed finite number of response rounds.
The two sides use the same protocol, with no architect choices. A response
family can depend on that side's own prior responses. This does not cover
adaptive stopping rules that depend on the other side's history.
-/

namespace Erdos118.SynchronizedRounds

open RamseyGame

universe u

inductive Protocol (X : Type u) : ℕ → Type u where
  | leaf (x : X) : Protocol X 0
  | response {n : ℕ} (F : ResponseFamily) (next : F.members → Protocol X n) :
      Protocol X (n + 1)

inductive Produces {X : Type u} (H : Set ℕ) : {n : ℕ} → Protocol X n → X → Prop where
  | leaf (x : X) : Produces H (.leaf x) x
  | response {n : ℕ} {F : ResponseFamily} {next : F.members → Protocol X n}
      (a : F.members) (ha : (↑a.1 : Set ℕ) ⊆ H) {x : X}
      (h : Produces H (next a) x) : Produces H (.response F next) x

noncomputable def pairGame {X : Type u} (B : SimpleGraph X) :
    {n : ℕ} → Protocol X n → Protocol X n → Game
  | 0, .leaf x, .leaf y => by
      classical
      exact .leaf (decide (B.Adj x y))
  | _ + 1, .response F f, .response G g =>
      .response F (fun a ↦ .response G (fun b ↦ pairGame B (f a) (g b)))

theorem triangle {X : Type u} (B : SimpleGraph X) {H : Set ℕ} (hH : H.Infinite)
    {n : ℕ} (R S T : Protocol X n)
    (hRS : Outcome H (pairGame B R S) true)
    (hRT : Outcome H (pairGame B R T) true)
    (hST : Outcome H (pairGame B S T) true) :
    ∃ r s t : X, Produces H R r ∧ Produces H S s ∧ Produces H T t ∧
      B.Adj r s ∧ B.Adj r t ∧ B.Adj s t := by
  classical
  induction n with
  | zero =>
    cases R with
    | leaf r =>
      cases S with
      | leaf s =>
        cases T with
        | leaf t =>
          exact ⟨r, s, t, .leaf r, .leaf s, .leaf t,
            of_decide_eq_true (outcome_leaf_iff.mp hRS),
            of_decide_eq_true (outcome_leaf_iff.mp hRT),
            of_decide_eq_true (outcome_leaf_iff.mp hST)⟩
  | succ n ih =>
    cases R with
    | response F f =>
      cases S with
      | response G g =>
        cases T with
        | response K k =>
          cases hRS with
          | response _ _ bRS _ hRS =>
            cases hRT with
            | response _ _ bRT _ hRT =>
              cases hST with
              | response _ _ bST _ hST =>
                obtain ⟨a, haH, hab⟩ := F.conservative_exists hH (max bRS bRT)
                have hRSa := hRS a haH
                  (fun z hz ↦ (le_max_left bRS bRT).trans_lt (hab z hz))
                have hRTa := hRT a haH
                  (fun z hz ↦ (le_max_right bRS bRT).trans_lt (hab z hz))
                cases hRSa with
                | response _ _ cRS _ hRSa =>
                  cases hRTa with
                  | response _ _ cRT _ hRTa =>
                    obtain ⟨b, hbH, hbb⟩ := G.conservative_exists hH (max cRS bST)
                    have hRSab := hRSa b hbH
                      (fun z hz ↦ (le_max_left cRS bST).trans_lt (hbb z hz))
                    have hSTb := hST b hbH
                      (fun z hz ↦ (le_max_right cRS bST).trans_lt (hbb z hz))
                    cases hSTb with
                    | response _ _ cST _ hSTb =>
                      obtain ⟨c, hcH, hcb⟩ := K.conservative_exists hH (max cRT cST)
                      have hRTac := hRTa c hcH
                        (fun z hz ↦ (le_max_left cRT cST).trans_lt (hcb z hz))
                      have hSTbc := hSTb c hcH
                        (fun z hz ↦ (le_max_right cRT cST).trans_lt (hcb z hz))
                      obtain ⟨r, s, t, hr, hs, ht, hrs, hrt, hst⟩ :=
                        ih (f a) (g b) (k c) hRSab hRTac hSTbc
                      exact ⟨r, s, t, .response a haH hr, .response b hbH hs,
                        .response c hcH ht, hrs, hrt, hst⟩

theorem not_blue {X : Type u} (B : SimpleGraph X) (hB : B.CliqueFree 3)
    {H : Set ℕ} (hH : H.Infinite) {n : ℕ} (T : Protocol X n) :
    ¬ Outcome H (pairGame B T T) true := by
  classical
  intro h
  obtain ⟨r, s, t, _, _, _, hrs, hrt, hst⟩ := triangle B hH T T T h h h
  exact hB {r, s, t} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hrs, hrt, hst⟩)

theorem red_outcome {X : Type u} (B : SimpleGraph X) (hB : B.CliqueFree 3)
    {n : ℕ} (T : Protocol X n) {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ Outcome H (pairGame B T T) false := by
  obtain ⟨H, hHN, hH, value, hval⟩ := dichotomy (pairGame B T T) N hN
  cases value with
  | false => exact ⟨H, hHN, hH, hval⟩
  | true => exact (not_blue B hB hH T hval).elim

theorem simultaneous_red {X : Type u} {I : Type} [Countable I] [Nonempty I]
    (B : SimpleGraph X) (hB : B.CliqueFree 3) (depth : I → ℕ)
    (T : (i : I) → Protocol X (depth i)) {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ ∀ i, Outcome H (pairGame B (T i) (T i)) false := by
  apply simultaneous_countable
    (fun i H ↦ Outcome H (pairGame B (T i) (T i)) false) ?_ ?_ hN
  · intro i H K hHK hK
    exact hK.almost_mono hHK
  · intro i M hM
    exact red_outcome B hB (T i) hM

end Erdos118.SynchronizedRounds
