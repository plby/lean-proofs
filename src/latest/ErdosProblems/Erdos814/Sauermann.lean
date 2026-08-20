import ErdosProblems.Erdos814.Arithmetic
import ErdosProblems.Erdos814.Basic
import ErdosProblems.Erdos814.Threshold
import ErdosProblems.Erdos814.Connectivity
import ErdosProblems.Erdos814.GoodSets
import ErdosProblems.Erdos814.Coloring

/-!
# Erdős 814: Sauermann's outer induction

This file packages the strong induction on the ambient vertex set.  Its one
graph-theoretic input is the counterexample-elimination theorem proved by the
dyadic-block and colouring argument.  Keeping the outer induction separate is
useful because the density parameter is an integer: in particular the same
proof includes the endpoint `k = 2`, `t = -1`.
-/

open Finset SimpleGraph

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The signed density hypothesis used throughout Sauermann's induction. -/
def SignedDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (A : Finset V) : Prop :=
  shortage k G A ≤ t

/-- The integral form of the desired small-core conclusion. -/
def SmallCoreExists (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) : Prop :=
  ∃ U : Finset V, U ⊆ A ∧ U.Nonempty ∧ HasMinDegreeOn G U k ∧
    uniformDen k * U.card ≤ (uniformDen k - 1) * A.card

lemma SmallCoreExists.of_isSmallCoreOn
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {A U : Finset V}
    (hU : IsSmallCoreOn G A k (uniformDen k) U) :
    SmallCoreExists G k A := by
  rcases hU with ⟨hUA, hmin, hsmall⟩
  exact ⟨U, hUA, hmin.1, hmin, hsmall⟩

lemma SmallCoreExists.mono_ambient
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {B A : Finset V}
    (hBA : B ⊆ A) (h : SmallCoreExists G k B) : SmallCoreExists G k A := by
  rcases h with ⟨U, hUB, hUne, hUmin, hsmall⟩
  refine ⟨U, hUB.trans hBA, hUne, hUmin, ?_⟩
  exact hsmall.trans (Nat.mul_le_mul_left (uniformDen k - 1) (card_le_card hBA))

lemma problemT_eq_Tmax_sub_one (k : ℕ) : problemT k = Tmax k - 1 := by
  rfl

lemma le_problemT_of_add_one_le_Tmax {k : ℕ} {t : ℤ}
    (ht : t + 1 ≤ Tmax k) : t ≤ problemT k := by
  rw [problemT_eq_Tmax_sub_one]
  omega

/-- The signed range `t+1≤Tmax` is strong enough to imply the exact
Problem-814 edge threshold. -/
lemma edgeThreshold_le_of_signedDensity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    edgeThreshold k A.card ≤ edgeCount G A := by
  have ht' : t ≤ problemT k := le_problemT_of_add_one_le_Tmax ht
  have hshort : shortage k G A ≤ problemT k := hedge.trans ht'
  have hcast := edgeThreshold_cast_eq k A.card hk hcard
  have hmulcast :
      ((((k - 1) * A.card : ℕ) : ℤ)) =
        (((k - 1 : ℕ) : ℤ) * (A.card : ℤ)) := by
    push_cast
    rfl
  have hcastle : (edgeThreshold k A.card : ℤ) ≤ (edgeCount G A : ℤ) := by
    rw [hcast, hmulcast]
    simpa [SignedDensity, shortage, add_comm] using hshort
  exact_mod_cast hcastle

/-- Feasibility of the signed density bound forces enough vertices for the
singleton instance of the local expansion inequality. -/
lemma card_ge_succ_of_signedDensity
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    k + 1 ≤ A.card := by
  exact card_ge_succ_of_edgeThreshold_le G k hk hcard
    (edgeThreshold_le_of_signedDensity G k t hk ht A hcard hedge)

/-- The precise induction hypothesis used to prove Claim 2.1. -/
def SmallerCoreHypothesis
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (A : Finset V) : Prop :=
  ∀ B : Finset V, B ⊂ A → k - 1 ≤ B.card →
    SignedDensity G k t B → SmallCoreExists G k B

/-- Claim 2.1.  If a deletion set violated local expansion, deleting it
would preserve the signed density bound and the induction hypothesis on the
remaining vertices would yield a small core. -/
lemma localExpansion_of_smallerCoreHypothesis
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (A : Finset V)
    (hcard : k - 1 ≤ A.card) (hlarge : k + 1 ≤ A.card)
    (hedge : SignedDensity G k t A)
    (hsmaller : SmallerCoreHypothesis G k t A)
    (hnosmall : ¬ SmallCoreExists G k A) :
    LocalExpansion G A k := by
  intro X hXne hXA hXcard
  by_contra hinc
  have hinc' : incidentCount G A X ≤ (k - 1) * X.card := by omega
  let B := A \ X
  have hBcard_eq : B.card = A.card - X.card := by
    simp [B, card_sdiff_of_subset hXA]
  have hBcard : k - 1 ≤ B.card := by
    have hrewrite : A.card - k + 1 = A.card - (k - 1) := by omega
    rw [hrewrite] at hXcard
    rw [hBcard_eq]
    omega
  have hBssub : B ⊂ A := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨sdiff_subset, ?_⟩
    intro hBA
    obtain ⟨x, hxX⟩ := hXne
    have hxA := hXA hxX
    have hxB : x ∈ B := hBA.symm ▸ hxA
    exact (mem_sdiff.mp hxB).2 hxX
  have hpot : 0 ≤ deletionPotential k G A X := by
    unfold deletionPotential
    have hincZ : (incidentCount G A X : ℤ) ≤
        (((k - 1 : ℕ) : ℤ) * (X.card : ℤ)) := by
      exact_mod_cast hinc'
    exact sub_nonneg.mpr hincZ
  have hBshort : SignedDensity G k t B := by
    have hs := shortage_sdiff k G hXA
    change shortage k G B ≤ t
    calc
      shortage k G B = shortage k G A - deletionPotential k G A X := hs
      _ ≤ shortage k G A := sub_le_self _ hpot
      _ ≤ t := hedge
  exact hnosmall <| SmallCoreExists.mono_ambient hBssub.subset
    (hsmaller B hBssub hBcard hBshort)

/-- Singleton local expansion is precisely the assertion that every ambient
vertex has degree at least `k`. -/
lemma hasMinDegreeOn_of_localExpansion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (A : Finset V) (hcard : k + 1 ≤ A.card)
    (hlocal : LocalExpansion G A k) :
    HasMinDegreeOn G A k := by
  have hAne : A.Nonempty := by
    apply card_pos.mp
    omega
  refine ⟨hAne, ?_⟩
  intro v hvA
  have hsingle : ({v} : Finset V).Nonempty := singleton_nonempty v
  have hsingleSub : ({v} : Finset V) ⊆ A := singleton_subset_iff.mpr hvA
  have hsingleCard : ({v} : Finset V).card ≤ A.card - k + 1 := by
    simp
  have h := hlocal {v} hsingle hsingleSub hsingleCard
  have hincident : incidentCount G A {v} = degreeOn G A v := by
    have hdel := edgeCount_sdiff_add_incidentCount G A {v}
    have herase := edgeCount_erase_add_degreeOn G hvA
    have hs : A \ {v} = A.erase v := by ext x; simp [and_comm]
    rw [hs] at hdel
    omega
  rw [hincident] at h
  simp only [card_singleton, Nat.mul_one] at h
  omega

/-- The graph-theoretic input consumed by the outer induction: all structural
properties forced in a minimal counterexample contradict the absence of a
small core. -/
def CounterexampleStep
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ (k : ℕ) (t : ℤ), 2 ≤ k → t + 1 ≤ Tmax k →
    ∀ A : Finset V, k - 1 ≤ A.card → SignedDensity G k t A →
      LocalExpansion G A k → HasMinDegreeOn G A k → ConnectedOn G A →
      SmallCoreExists G k A

/-- Strong induction on `A.card`, abstracting only the final
counterexample-elimination argument. -/
theorem sauermann_uniform_on_of_step
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hstep : CounterexampleStep G)
    (k : ℕ) (t : ℤ) (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hedge : SignedDensity G k t A) :
    SmallCoreExists G k A := by
  revert hcard hedge
  refine Finset.strongInductionOn A ?_
  intro A ih hcard hedge
  by_contra hnosmall
  have hsmaller : SmallerCoreHypothesis G k t A := by
    intro B hBA hBcard hBedge
    exact ih B hBA hBcard hBedge
  have hlarge := card_ge_succ_of_signedDensity G k t hk ht A hcard hedge
  have hlocal := localExpansion_of_smallerCoreHypothesis G k t hk A
    hcard hlarge hedge hsmaller hnosmall
  have hmin := hasMinDegreeOn_of_localExpansion G k A hlarge hlocal
  have hD : 2 ≤ uniformDen k := by
    simp only [uniformDen]
    have : 0 < k ^ 3 := pow_pos (by omega) _
    nlinarith
  have hnoCore : NoSmallCoreOn G A k (uniformDen k) := by
    intro h
    rcases h with ⟨U, hUA, hUmin, hsmall⟩
    exact hnosmall ⟨U, hUA, hUmin.1, hUmin, hsmall⟩
  have hconn := connectedOn_of_noSmallCoreOn G hD hmin hnoCore
  exact hnosmall (hstep k t hk ht A hcard hedge hlocal hmin hconn)

/-- Sauermann's theorem in its uniform, signed form.  The hypothesis
`t + 1 ≤ Tmax k` includes the endpoint `k = 2`, `t = -1`; no natural-number
subtraction is used in the density assumption. -/
theorem sauermann_uniform_on
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} {t : ℤ} (hk : 2 ≤ k) (ht : t + 1 ≤ Tmax k)
    (A : Finset V) (hcard : k - 1 ≤ A.card)
    (hshort : shortage k G A ≤ t) :
    ∃ U : Finset V, U ⊆ A ∧ U.Nonempty ∧ HasMinDegreeOn G U k ∧
      uniformDen k * U.card ≤ (uniformDen k - 1) * A.card := by
  have hstep : CounterexampleStep G := by
    intro k t hk ht A hcard hshort hlocal hmin hconn
    obtain ⟨U, hU⟩ := exists_small_core_of_localExpansion G k t hk ht A hcard
      hshort hlocal hmin hconn
    exact SmallCoreExists.of_isSmallCoreOn hU
  have hDensity : SignedDensity G k t A := hshort
  simpa only [SmallCoreExists] using
    sauermann_uniform_on_of_step G hstep k t hk ht A hcard hDensity

end Erdos814
