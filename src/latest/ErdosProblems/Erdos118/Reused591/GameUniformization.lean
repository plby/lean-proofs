import ErdosProblems.Erdos590
import ErdosProblems.Erdos118.Reused591.GameFusion
import Mathlib.Order.Extension.Well

namespace Erdos118.Reused591

/-!
# Conservative uniformization of finite-response games

This is the general uniformization lemma in the positive mathematical
proof of Erdős problem 591. The game-specific parser, large-set
construction, and triangle amalgamation are separate obligations.
-/

namespace Erdos591.Positive.Game

open Set
open Erdos590.Larson.NashWilliams

inductive PositionKind where
  | terminal (architectWins : Bool)
  | architect
  | builder
  deriving DecidableEq

/-- A countable closed game with thin finite responses. `next q p`
means that `q` is an immediate successor of `p`, so the well-founded
relation points in the direction of backward induction. The response
existence field is the part of the block property used by this lemma.
-/
structure FiniteResponseGame (P : Type*) (N : Set ℕ) where
  kind : P → PositionKind
  next : P → P → Prop
  wellFounded : WellFounded next
  architect_move : ∀ p, kind p = .architect → ∃ q, next q p
  family : P → Set (Finset ℕ)
  response : P → Finset ℕ → P
  response_next : ∀ p u, kind p = .builder → u ∈ family p → next (response p u) p
  thin : ∀ p, kind p = .builder → FinThin (family p)
  threshold : P → ℕ
  response_exists : ∀ p, kind p = .builder → ∀ M : Set ℕ,
    M ⊆ N → M.Infinite → (∀ x ∈ M, threshold p < x) →
    ∃ u, u ∈ family p ∧ (↑u : Set ℕ) ⊆ M

namespace FiniteResponseGame

variable {P : Type*} {N : Set ℕ} (G : FiniteResponseGame P N)

theorem response_exists_above {H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (p : P) (hp : G.kind p = .builder) (b : ℕ) :
    ∃ u, u ∈ G.family p ∧ (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, b < x := by
  let M := H \ Set.Iic (max b (G.threshold p))
  have hM : M.Infinite := hH.sdiff (Set.finite_Iic _)
  obtain ⟨u, hu, huM⟩ := G.response_exists p hp M
    (fun x hx => hHN hx.1) hM (by
      intro x hx
      exact lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hx.2))
  refine ⟨u, hu, fun x hx => (huM hx).1, ?_⟩
  intro x hx
  exact lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge (huM hx).2)

/-- The local value equations after conservative uniformization. -/
def ValueSystem (H : Set ℕ) (b : P → ℕ) (v : P → Bool) : Prop :=
  (∀ p w, G.kind p = .terminal w → v p = w) ∧
  (∀ p, G.kind p = .architect →
    (v p = true ↔ ∃ q, G.next q p ∧ v q = true)) ∧
  (∀ p, G.kind p = .builder → ∀ u, u ∈ G.family p →
    (↑u : Set ℕ) ⊆ H → (∀ x ∈ u, b p < x) → v (G.response p u) = v p) ∧
  (∀ p, G.kind p = .builder →
    ∃ u, u ∈ G.family p ∧ (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, b p < x)

/-- All positions can be assigned coherent Boolean values on one
infinite set of conservative inputs. The bound is allowed to depend on
the whole position, rather than only its depth. -/
theorem exists_valueSystem [Countable P] (hN : N.Infinite) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ (b : P → ℕ) (v : P → Bool),
      G.ValueSystem H b v := by
  classical
  let : IsWellFounded P G.next := ⟨G.wellFounded⟩
  let : LinearOrder P := IsWellFounded.wellOrderExtension G.next
  let : WellFoundedLT P := IsWellFounded.wellOrderExtension.isWellFounded_lt G.next
  have hlt {q p : P} (h : G.next q p) : q < p :=
    Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel h)
  let Local (p : P) (prev : ∀ q, q < p → Bool) (M : Set ℕ) (v : Bool) : Prop :=
    (∀ w, G.kind p = .terminal w → v = w) ∧
    (G.kind p = .architect →
      (v = true ↔ ∃ q, ∃ h : G.next q p, prev q (hlt h) = true)) ∧
    (∀ hp : G.kind p = .builder, ∀ u, ∀ hu : u ∈ G.family p,
      (↑u : Set ℕ) ⊆ M → prev (G.response p u) (hlt (G.response_next p u hp hu)) = v)
  have hstep (p : P) (prev : ∀ q, q < p → Bool) (M : Set ℕ)
      (_hMN : M ⊆ N) (hM : M.Infinite) :
      ∃ L v, L ⊆ M ∧ L.Infinite ∧ Local p prev L v := by
    cases hp : G.kind p with
    | terminal w =>
        refine ⟨M, w, Set.Subset.rfl, hM, ?_⟩
        simp [Local, hp]
    | architect =>
        refine ⟨M, decide (∃ q, ∃ h : G.next q p, prev q (hlt h) = true),
          Set.Subset.rfl, hM, ?_⟩
        simp [Local, hp]
    | builder =>
        let color (u : Finset ℕ) : Bool :=
          if hu : u ∈ G.family p then
            prev (G.response p u) (hlt (G.response_next p u hp hu))
          else false
        obtain ⟨L, hLM, hL, v, hc⟩ :=
          nashWilliams_two (G.family p) (G.thin p hp) color hM
        refine ⟨L, v, hLM, hL, ?_⟩
        refine ⟨?_, ?_, ?_⟩
        · intro w hw
          simp [hp] at hw
        · intro ha
          simp [hp] at ha
        · intro _ u hu huL
          simpa [color, hu] using hc u hu huL
  obtain ⟨v, s, hs, hchain⟩ := fusion_recursion hN Local hstep
  obtain ⟨H, hHN, hH, hHs⟩ := pseudointersection_chain hN s
    (fun p => (hs p).2.1) (fun p => (hs p).1) hchain
  choose c hc using fun p => (hHs p).exists_tail_bound
  let b (p : P) := max (c p) (G.threshold p)
  refine ⟨H, hHN, hH, b, v, ?_, ?_, ?_, ?_⟩
  · intro p w hp
    exact (hs p).2.2.1 w hp
  · intro p hp
    simpa only [exists_prop] using (hs p).2.2.2.1 hp
  · intro p hp u hu huH hub
    apply (hs p).2.2.2.2 hp u hu
    intro x hxu
    apply hc p x (huH hxu)
    exact lt_of_le_of_lt (le_max_left _ _) (hub x hxu)
  · intro p hp
    exact G.response_exists_above hHN hH p hp (b p)

/-- Thinning the input set and increasing the positional bounds preserve
the value equations, including the availability of legal responses. -/
theorem ValueSystem.mono {H H' : Set ℕ} {b b' : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) (hHN : H ⊆ N) (hH' : H'.Infinite)
    (hH'H : H' ⊆ H) (hb : ∀ p, b p ≤ b' p) : G.ValueSystem H' b' v := by
  refine ⟨hv.1, hv.2.1, ?_, ?_⟩
  · intro p hp u hu huH hub
    exact hv.2.2.1 p hp u hu (huH.trans hH'H)
      (fun x hx => lt_of_le_of_lt (hb p) (hub x hx))
  · intro p hp
    exact G.response_exists_above (hH'H.trans hHN) hH' p hp (b' p)

/-- Histories have finite sets of prefixes. Taking a maximum over these
sets gives bounds that are nondecreasing along legal plays. -/
theorem exists_monotone_valueSystem [Countable P] (hN : N.Infinite)
    (past : P → Finset P) (hself : ∀ p, p ∈ past p)
    (hnext : ∀ p q, G.next q p → past p ⊆ past q) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ (b : P → ℕ) (v : P → Bool),
      G.ValueSystem H b v ∧ (∀ p q, G.next q p → b p ≤ b q) := by
  obtain ⟨H, hHN, hH, c, v, hv⟩ := G.exists_valueSystem hN
  let b (p : P) := (past p).sup c
  refine ⟨H, hHN, hH, b, v, ?_, ?_⟩
  · exact hv.mono G hHN hH Set.Subset.rfl (fun p => Finset.le_sup (hself p))
  · intro p q hpq
    exact Finset.sup_mono (hnext p q hpq)

/-- A legal architect move, or a builder response from the prescribed
infinite set above the bound at the current position. This relation is
oriented forwards along plays. -/
inductive ConservativeStep (H : Set ℕ) (b : P → ℕ) : P → P → Prop
  | architect (p q : P) (hp : G.kind p = .architect) (hq : G.next q p) :
      ConservativeStep H b p q
  | builder (p : P) (u : Finset ℕ) (hp : G.kind p = .builder)
      (hu : u ∈ G.family p) (huH : (↑u : Set ℕ) ⊆ H)
      (hub : ∀ x ∈ u, b p < x) : ConservativeStep H b p (G.response p u)

theorem ConservativeStep.next {H : Set ℕ} {b : P → ℕ} {p q : P}
    (h : G.ConservativeStep H b p q) : G.next q p := by
  cases h with
  | architect _ _ hq => exact hq
  | builder u hp hu _ _ => exact G.response_next p u hp hu

theorem conservative_wellFounded (H : Set ℕ) (b : P → ℕ) :
    WellFounded (fun q p => G.ConservativeStep H b p q) :=
  G.wellFounded.mono fun _ _ h => h.next G

/-- The architect chooses only at architect positions; the proof of
legality is included, so a strategy cannot manufacture a dead end. -/
structure ArchitectStrategy where
  move : ∀ p, G.kind p = .architect → P
  legal : ∀ p hp, G.next (move p hp) p

def FollowStep (σ : G.ArchitectStrategy) (H : Set ℕ) (b : P → ℕ)
    (p q : P) : Prop :=
  G.ConservativeStep H b p q ∧ ∀ hp : G.kind p = .architect, q = σ.move p hp

/-- Against a fixed architect strategy, a conservative terminal play
exists from every position. Closedness is used here, not an assumption
that players voluntarily stop. -/
theorem terminal_reachable {H : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) (σ : G.ArchitectStrategy) (p : P) :
    ∃ q w, Relation.ReflTransGen (G.FollowStep σ H b) p q ∧
      G.kind q = .terminal w := by
  apply G.wellFounded.induction p
  intro p ih
  cases hp : G.kind p with
  | terminal w => exact ⟨p, w, .refl, hp⟩
  | architect =>
      obtain ⟨q, w, hpath, hq⟩ := ih (σ.move p hp) (σ.legal p hp)
      refine ⟨q, w, hpath.head ?_, hq⟩
      exact ⟨.architect p (σ.move p hp) hp (σ.legal p hp), fun _ => rfl⟩
  | builder =>
      obtain ⟨u, hu, huH, hub⟩ := hv.2.2.2 p hp
      obtain ⟨q, w, hpath, hq⟩ := ih (G.response p u) (G.response_next p u hp hu)
      refine ⟨q, w, hpath.head ?_, hq⟩
      refine ⟨.builder p u hp hu huH hub, ?_⟩
      intro ha
      simp [hp] at ha

def ArchitectWins (H : Set ℕ) (b : P → ℕ) (σ : G.ArchitectStrategy) (p : P) : Prop :=
  ∀ q w, Relation.ReflTransGen (G.FollowStep σ H b) p q →
    G.kind q = .terminal w → w = true

def AllBuilderWins (H : Set ℕ) (b : P → ℕ) (p : P) : Prop :=
  ∀ q w, Relation.ReflTransGen (G.ConservativeStep H b) p q →
    G.kind q = .terminal w → w = false

theorem ValueSystem.false_step {H : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) {p q : P}
    (hpv : v p = false) (hpq : G.ConservativeStep H b p q) : v q = false := by
  cases hpq with
  | architect q hp hq =>
      cases hqv : v q with
      | false => rfl
      | true =>
          have htrue := (hv.2.1 p hp).2 ⟨q, hq, hqv⟩
          simp [hpv] at htrue
  | builder u hp hu huH hub =>
      exact (hv.2.2.1 p hp u hu huH hub).trans hpv

theorem ValueSystem.allBuilderWins {H : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) {p : P} (hp : v p = false) :
    G.AllBuilderWins H b p := by
  intro q w hpq hq
  have hval : v q = false := by
    clear hq
    induction hpq with
    | refl => exact hp
    | tail _ hstep ih => exact hv.false_step G ih hstep
  exact (hv.1 q w hq).symm.trans hval

/-- One strategy preserves the value `true` simultaneously from every
true-valued position. At other positions it chooses an arbitrary legal
move. -/
theorem ValueSystem.exists_preserving_strategy {H : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) :
    ∃ σ : G.ArchitectStrategy,
      ∀ p hp, v p = true → v (σ.move p hp) = true := by
  classical
  have hm (p : P) (hp : G.kind p = .architect) :
      ∃ q, G.next q p ∧ (v p = true → v q = true) := by
    by_cases hvp : v p = true
    · obtain ⟨q, hq, hqv⟩ := (hv.2.1 p hp).1 hvp
      exact ⟨q, hq, fun _ => hqv⟩
    · obtain ⟨q, hq⟩ := G.architect_move p hp
      exact ⟨q, hq, fun h => (hvp h).elim⟩
  choose move hmove using hm
  exact ⟨⟨move, fun p hp => (hmove p hp).1⟩, fun p hp => (hmove p hp).2⟩

theorem ValueSystem.architectWins {H : Set ℕ} {b : P → ℕ} {v : P → Bool}
    (hv : G.ValueSystem H b v) (σ : G.ArchitectStrategy)
    (hσ : ∀ p hp, v p = true → v (σ.move p hp) = true)
    {p : P} (hp : v p = true) : G.ArchitectWins H b σ p := by
  intro q w hpq hq
  have hval : v q = true := by
    clear hq
    induction hpq with
    | refl => exact hp
    | @tail q r _ hstep ih =>
        obtain ⟨hstep, hfollow⟩ := hstep
        cases hstep with
        | architect r hkind _ =>
            rw [hfollow hkind]
            exact hσ q hkind ih
        | builder u hkind hu huH hub =>
            exact (hv.2.2.1 q hkind u hu huH hub).trans ih
  exact (hv.1 q w hq).symm.trans hval

/-- The conservative-game dichotomy, with monotone history bounds.
The second alternative quantifies over every architect choice, not just
over the plays of one builder strategy. -/
theorem conservative_uniformization [Countable P] (hN : N.Infinite)
    (past : P → Finset P) (hself : ∀ p, p ∈ past p)
    (hnext : ∀ p q, G.next q p → past p ⊆ past q) (root : P) :
    ∃ H, H ⊆ N ∧ H.Infinite ∧ ∃ (b : P → ℕ) (v : P → Bool),
      G.ValueSystem H b v ∧ (∀ p q, G.next q p → b p ≤ b q) ∧
      ((∃ σ : G.ArchitectStrategy, G.ArchitectWins H b σ root) ∨
        G.AllBuilderWins H b root) := by
  obtain ⟨H, hHN, hH, b, v, hv, hb⟩ :=
    G.exists_monotone_valueSystem hN past hself hnext
  refine ⟨H, hHN, hH, b, v, hv, hb, ?_⟩
  cases hroot : v root with
  | false => exact Or.inr (hv.allBuilderWins G hroot)
  | true =>
      obtain ⟨σ, hσ⟩ := hv.exists_preserving_strategy G
      exact Or.inl ⟨σ, hv.architectWins G σ hσ hroot⟩

#print axioms conservative_uniformization

end FiniteResponseGame

end Erdos591.Positive.Game

end Erdos118.Reused591
