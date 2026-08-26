import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Embedding.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Order
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Rainbow bipartite submatrices

Sanitized standalone staging file for the finite combinatorial lemma used in
Erdos Problem 593.  No project-local declarations are imported.
-/

open Function

namespace Erdos593
namespace RainbowBipartite

universe u

namespace Counting

universe v w

/-- A finite union of event sets cannot cover a larger sample space. -/
theorem exists_avoiding_of_event_card_le
    {Omega : Type v} {Iota : Type w} [Fintype Omega] [Fintype Iota]
    (bad : Iota → Omega → Prop) [∀ i, DecidablePred (bad i)]
    (bound : ℕ)
    (hbad : ∀ i, Fintype.card {sample : Omega // bad i sample} ≤ bound)
    (hsmall : Fintype.card Iota * bound < Fintype.card Omega) :
    ∃ sample : Omega, ∀ i, ¬ bad i sample := by
  classical
  by_contra hcover
  push Not at hcover
  let forget : (Σ i, {sample : Omega // bad i sample}) → Omega := fun z ↦ z.2.1
  have hsurj : Function.Surjective forget := by
    intro sample
    obtain ⟨i, hi⟩ := hcover sample
    exact ⟨⟨i, ⟨sample, hi⟩⟩, rfl⟩
  have hcard : Fintype.card Omega ≤ Fintype.card (Σ i, {sample : Omega // bad i sample}) :=
    Fintype.card_le_of_surjective forget hsurj
  have hlt : Fintype.card Omega < Fintype.card Omega := by
    calc
      Fintype.card Omega
          ≤ Fintype.card (Σ i, {sample : Omega // bad i sample}) := hcard
      _ = ∑ i, Fintype.card {sample : Omega // bad i sample} := Fintype.card_sigma
      _ ≤ ∑ _i : Iota, bound := by
        gcongr with i
        exact hbad i
      _ = Fintype.card Iota * bound := by simp
      _ < Fintype.card Omega := hsmall
  exact (Nat.lt_irrefl _ hlt)

/-- If a predicate on functions has at most `d` choices in one distinguished
coordinate after all other coordinates are fixed, its total event set has the
corresponding product bound. -/
theorem card_function_event_le_of_fiber_le
    {Iota : Type v} {Alpha : Type w} [Fintype Iota] [DecidableEq Iota]
    [Fintype Alpha] (k : Iota) (P : (Iota → Alpha) → Prop) [DecidablePred P]
    (d : ℕ)
    (hfiber : ∀ rest : ({j : Iota // j ≠ k} → Alpha),
      Fintype.card {a : Alpha // P ((Equiv.funSplitAt k Alpha).symm (a, rest))} ≤ d) :
    Fintype.card {f : Iota → Alpha // P f} ≤
      d * Fintype.card Alpha ^ (Fintype.card Iota - 1) := by
  classical
  let R := ({j : Iota // j ≠ k} → Alpha)
  let split : (Iota → Alpha) ≃ R × Alpha :=
    (Equiv.funSplitAt k Alpha).trans (Equiv.prodComm Alpha R)
  let p : R → Alpha → Prop := fun rest a ↦ P (split.symm (rest, a))
  let eventEquiv : {f : Iota → Alpha // P f} ≃ {z : R × Alpha // p z.1 z.2} :=
    split.subtypeEquiv (by
      intro f
      simp [p])
  have hremaining : Fintype.card {j : Iota // j ≠ k} = Fintype.card Iota - 1 := by
    simp
  calc
    Fintype.card {f : Iota → Alpha // P f}
        = Fintype.card {z : R × Alpha // p z.1 z.2} :=
          Fintype.card_congr eventEquiv
    _ = Fintype.card (Σ rest : R, {a : Alpha // p rest a}) :=
      Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype p)
    _ = ∑ rest : R, Fintype.card {a : Alpha // p rest a} := Fintype.card_sigma
    _ ≤ ∑ _rest : R, d := by
      gcongr with rest
      have heq :
          Fintype.card {a : Alpha // p rest a} =
            Fintype.card {a : Alpha //
              P ((Equiv.funSplitAt k Alpha).symm (a, rest))} := by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivRight
        intro a
        rfl
      exact heq.trans_le (hfiber rest)
    _ = Fintype.card R * d := by simp
    _ = d * Fintype.card Alpha ^ (Fintype.card Iota - 1) := by
      simp [R, hremaining, Nat.mul_comm]

end Counting

/-- A coloring of the balanced complete bipartite graph is locally bounded by
`t` when each color appears on fewer than `t` edges at every left and right
vertex. -/
def LocallyBounded {q : ℕ} {Gamma : Type u} (t : ℕ)
    (color : Fin q → Fin q → Gamma) : Prop :=
  (∀ x a, Nat.card {y : Fin q // color x y = a} < t) ∧
    (∀ y a, Nat.card {x : Fin q // color x y = a} < t)

/-- A pair of injective selections of rows and columns is rainbow when all
colors in the selected square are pairwise distinct. -/
def IsRainbow {n q : ℕ} {Gamma : Type u} (color : Fin q → Fin q → Gamma)
    (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q) : Prop :=
  Injective fun ij : Fin n × Fin n ↦ color (left ij.1) (right ij.2)

private abbrev Coordinate (n : ℕ) := Fin n ⊕ Fin n

private abbrev EdgePosition (n : ℕ) := Fin n × Fin n

private abbrev BadIndex (n : ℕ) :=
  EdgePosition n ⊕ (EdgePosition n ⊕ (EdgePosition n × EdgePosition n))

private def Bad {n q : ℕ} {Gamma : Type u} (color : Fin q → Fin q → Gamma) :
    BadIndex n → (Coordinate n → Fin q) → Prop
  | Sum.inl (i, i'), sample =>
      i ≠ i' ∧ sample (Sum.inl i) = sample (Sum.inl i')
  | Sum.inr (Sum.inl (j, j')), sample =>
      j ≠ j' ∧ sample (Sum.inr j) = sample (Sum.inr j')
  | Sum.inr (Sum.inr (e, e')), sample =>
      e ≠ e' ∧
        color (sample (Sum.inl e.1)) (sample (Sum.inr e.2)) =
          color (sample (Sum.inl e'.1)) (sample (Sum.inr e'.2))

private theorem funSplitAt_symm_apply_self
    {Iota Alpha : Type*} [DecidableEq Iota] (k : Iota) (a : Alpha)
    (rest : {j : Iota // j ≠ k} → Alpha) :
    (Equiv.funSplitAt k Alpha).symm (a, rest) k = a := by
  simp [Equiv.funSplitAt_symm_apply]

private theorem funSplitAt_symm_apply_of_ne
    {Iota Alpha : Type*} [DecidableEq Iota] (k j : Iota) (hjk : j ≠ k)
    (a : Alpha) (rest : {j : Iota // j ≠ k} → Alpha) :
    (Equiv.funSplitAt k Alpha).symm (a, rest) j = rest ⟨j, hjk⟩ := by
  simp [Equiv.funSplitAt_symm_apply, hjk]

/-- Manuscript Lemma 3.1, in exact finite form and with an arbitrary color
type. -/
theorem exists_rainbow_bipartite_submatrix (n t : ℕ) (hn : 0 < n) (ht : 0 < t) :
    ∃ q : ℕ, ∀ (Gamma : Type u) (color : Fin q → Fin q → Gamma),
      LocallyBounded t color →
        ∃ (left : Fin n ↪ Fin q) (right : Fin n ↪ Fin q),
          IsRainbow color left right := by
  classical
  let q := Fintype.card (BadIndex n) * t + 1
  refine ⟨q, ?_⟩
  intro Gamma color hlocal
  have hq : 0 < q := by simp [q]
  have hbad : ∀ index : BadIndex n,
      Fintype.card {sample : Coordinate n → Fin q // Bad color index sample} ≤
        t * q ^ (Fintype.card (Coordinate n) - 1) := by
    intro index
    rcases index with leftIndex | rightOrColor
    · rcases leftIndex with ⟨i, i'⟩
      by_cases hii : i = i'
      · simp [Bad, hii]
      · have hcount := Counting.card_function_event_le_of_fiber_le
          (Iota := Coordinate n) (Alpha := Fin q)
          (k := Sum.inl i') (P := Bad color (Sum.inl (i, i'))) t (by
            intro rest
            have hne : (Sum.inl i : Coordinate n) ≠ Sum.inl i' := by simp [hii]
            have hpred : ∀ a : Fin q,
                Bad color (Sum.inl (i, i'))
                    ((Equiv.funSplitAt (Sum.inl i') (Fin q)).symm (a, rest)) ↔
                  rest ⟨Sum.inl i, hne⟩ = a := by
              intro a
              simp only [Bad]
              rw [funSplitAt_symm_apply_of_ne _ _ hne,
                funSplitAt_symm_apply_self]
              simp [hii]
            calc
              Fintype.card {a : Fin q //
                  Bad color (Sum.inl (i, i'))
                    ((Equiv.funSplitAt (Sum.inl i') (Fin q)).symm (a, rest))} =
                  Fintype.card {a : Fin q // rest ⟨Sum.inl i, hne⟩ = a} :=
                Fintype.card_congr (Equiv.subtypeEquivRight hpred)
              _ = 1 := by simp
              _ ≤ t := by omega)
        simpa using! hcount
    · rcases rightOrColor with rightIndex | colorIndex
      · rcases rightIndex with ⟨j, j'⟩
        by_cases hjj : j = j'
        · simp [Bad, hjj]
        · have hcount := Counting.card_function_event_le_of_fiber_le
            (Iota := Coordinate n) (Alpha := Fin q)
            (k := Sum.inr j') (P := Bad color (Sum.inr (Sum.inl (j, j')))) t (by
              intro rest
              have hne : (Sum.inr j : Coordinate n) ≠ Sum.inr j' := by simp [hjj]
              have hpred : ∀ a : Fin q,
                  Bad color (Sum.inr (Sum.inl (j, j')))
                      ((Equiv.funSplitAt (Sum.inr j') (Fin q)).symm (a, rest)) ↔
                    rest ⟨Sum.inr j, hne⟩ = a := by
                intro a
                simp only [Bad]
                rw [funSplitAt_symm_apply_of_ne _ _ hne,
                  funSplitAt_symm_apply_self]
                simp [hjj]
              calc
                Fintype.card {a : Fin q //
                    Bad color (Sum.inr (Sum.inl (j, j')))
                      ((Equiv.funSplitAt (Sum.inr j') (Fin q)).symm (a, rest))} =
                    Fintype.card {a : Fin q // rest ⟨Sum.inr j, hne⟩ = a} :=
                  Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                _ = 1 := by simp
                _ ≤ t := by omega)
          simpa using! hcount
      · rcases colorIndex with ⟨e, e'⟩
        by_cases heq : e = e'
        · simp [Bad, heq]
        · by_cases hright : e.2 = e'.2
          · have hleft : e.1 ≠ e'.1 := by
              intro h
              apply heq
              exact Prod.ext h hright
            have hcount := Counting.card_function_event_le_of_fiber_le
              (Iota := Coordinate n) (Alpha := Fin q)
              (k := Sum.inl e'.1)
              (P := Bad color (Sum.inr (Sum.inr (e, e')))) t (by
                intro rest
                have hL : (Sum.inl e.1 : Coordinate n) ≠ Sum.inl e'.1 := by
                  simp [hleft]
                have hR : (Sum.inr e.2 : Coordinate n) ≠ Sum.inl e'.1 := by simp
                have hR' : (Sum.inr e'.2 : Coordinate n) ≠ Sum.inl e'.1 := by simp
                let x : Fin q := rest ⟨Sum.inl e.1, hL⟩
                let y : Fin q := rest ⟨Sum.inr e.2, hR⟩
                let target : Gamma := color x y
                have hy : rest ⟨Sum.inr e'.2, hR'⟩ = y := by
                  dsimp only [y]
                  congr 1
                  apply Subtype.ext
                  simp [hright]
                have hpred : ∀ a : Fin q,
                    Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inl e'.1) (Fin q)).symm (a, rest)) ↔
                      color a y = target := by
                  intro a
                  simp only [Bad]
                  rw [funSplitAt_symm_apply_of_ne _ _ hL,
                    funSplitAt_symm_apply_of_ne _ _ hR,
                    funSplitAt_symm_apply_self,
                    funSplitAt_symm_apply_of_ne _ _ hR', hy]
                  simp only [x, y, target, eq_comm]
                  exact and_iff_right heq
                have hlocalCard :
                    Fintype.card {a : Fin q // color a y = target} < t := by
                  simpa only [Nat.card_eq_fintype_card] using! hlocal.2 y target
                calc
                  Fintype.card {a : Fin q //
                      Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inl e'.1) (Fin q)).symm (a, rest))} =
                      Fintype.card {a : Fin q // color a y = target} :=
                    Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                  _ ≤ t := hlocalCard.le)
            simpa using! hcount
          · have hcount := Counting.card_function_event_le_of_fiber_le
              (Iota := Coordinate n) (Alpha := Fin q)
              (k := Sum.inr e'.2)
              (P := Bad color (Sum.inr (Sum.inr (e, e')))) t (by
                intro rest
                have hL : (Sum.inl e.1 : Coordinate n) ≠ Sum.inr e'.2 := by simp
                have hL' : (Sum.inl e'.1 : Coordinate n) ≠ Sum.inr e'.2 := by simp
                have hR : (Sum.inr e.2 : Coordinate n) ≠ Sum.inr e'.2 := by
                  simp [hright]
                let x : Fin q := rest ⟨Sum.inl e.1, hL⟩
                let x' : Fin q := rest ⟨Sum.inl e'.1, hL'⟩
                let y : Fin q := rest ⟨Sum.inr e.2, hR⟩
                let target : Gamma := color x y
                have hpred : ∀ a : Fin q,
                    Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inr e'.2) (Fin q)).symm (a, rest)) ↔
                      color x' a = target := by
                  intro a
                  simp only [Bad]
                  rw [funSplitAt_symm_apply_of_ne _ _ hL,
                    funSplitAt_symm_apply_of_ne _ _ hR,
                    funSplitAt_symm_apply_of_ne _ _ hL',
                    funSplitAt_symm_apply_self]
                  simp only [x, x', y, target, eq_comm]
                  exact and_iff_right heq
                have hlocalCard :
                    Fintype.card {a : Fin q // color x' a = target} < t := by
                  simpa only [Nat.card_eq_fintype_card] using! hlocal.1 x' target
                calc
                  Fintype.card {a : Fin q //
                      Bad color (Sum.inr (Sum.inr (e, e')))
                        ((Equiv.funSplitAt (Sum.inr e'.2) (Fin q)).symm (a, rest))} =
                      Fintype.card {a : Fin q // color x' a = target} :=
                    Fintype.card_congr (Equiv.subtypeEquivRight hpred)
                  _ ≤ t := hlocalCard.le)
            simpa using! hcount
  have hcoord : 0 < Fintype.card (Coordinate n) :=
    Fintype.card_pos_iff.mpr ⟨Sum.inl ⟨0, hn⟩⟩
  have hsmall :
      Fintype.card (BadIndex n) *
          (t * q ^ (Fintype.card (Coordinate n) - 1)) <
        Fintype.card (Coordinate n → Fin q) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    have hcoeff : Fintype.card (BadIndex n) * t < q := by simp [q]
    have hmul :
        (Fintype.card (BadIndex n) * t) *
            q ^ (Fintype.card (Coordinate n) - 1) <
          q * q ^ (Fintype.card (Coordinate n) - 1) := by
      exact Nat.mul_lt_mul_of_pos_right hcoeff (pow_pos hq _)
    calc
      Fintype.card (BadIndex n) *
          (t * q ^ (Fintype.card (Coordinate n) - 1)) =
        (Fintype.card (BadIndex n) * t) *
          q ^ (Fintype.card (Coordinate n) - 1) := by ring
      _ < q * q ^ (Fintype.card (Coordinate n) - 1) := hmul
      _ = q ^ (Fintype.card (Coordinate n) - 1 + 1) := by
        rw [pow_succ]
        ring
      _ = q ^ Fintype.card (Coordinate n) := by
        have hcard : Fintype.card (Coordinate n) - 1 + 1 =
            Fintype.card (Coordinate n) := by omega
        rw [hcard]
  obtain ⟨sample, hsample⟩ :=
    Counting.exists_avoiding_of_event_card_le
      (bad := Bad color)
      (bound := t * q ^ (Fintype.card (Coordinate n) - 1)) hbad hsmall
  have hleftInjective : Injective (fun i : Fin n ↦ sample (Sum.inl i)) := by
    intro i i' hii
    by_contra hne
    exact hsample (Sum.inl (i, i')) ⟨hne, hii⟩
  have hrightInjective : Injective (fun j : Fin n ↦ sample (Sum.inr j)) := by
    intro j j' hjj
    by_contra hne
    exact hsample (Sum.inr (Sum.inl (j, j'))) ⟨hne, hjj⟩
  let left : Fin n ↪ Fin q := ⟨fun i ↦ sample (Sum.inl i), hleftInjective⟩
  let right : Fin n ↪ Fin q := ⟨fun j ↦ sample (Sum.inr j), hrightInjective⟩
  refine ⟨left, right, ?_⟩
  intro e e' he
  by_contra hne
  exact hsample (Sum.inr (Sum.inr (e, e'))) ⟨hne, he⟩

end RainbowBipartite
end Erdos593
