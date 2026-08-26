import ErdosProblems.Erdos788.FinitePrediction
import ErdosProblems.Erdos788.ExtractorInterface

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sequential prediction from total variation

This file packages the finite hybrid argument for a tuple over `ZMod p`.
A context is retained throughout the chain, so it can later carry the
Trevisan seed.
-/

namespace Erdos788

open scoped BigOperators

namespace FinDist

/-- The first `i` entries of a finite tuple. -/
def tuplePrefix {p r : ℕ} (i : Fin r) (z : FFVec p r) :
    FFVec p i.val := fun j ↦
  z (Fin.castLE (Nat.le_of_lt i.isLt) j)

/-- Split a tuple at its last entry while retaining an external context. -/
def lastSplitEquiv (Context : Type*) (p n : ℕ) :
    Context × FFVec p (n + 1) ≃
      (Context × FFVec p n) × ZMod p :=
  (Equiv.prodCongr (Equiv.refl Context)
    (Fin.succFunEquiv (ZMod p) n)).trans
      (Equiv.prodAssoc Context (FFVec p n) (ZMod p)).symm

@[simp]
theorem lastSplitEquiv_apply
    {Context : Type*} {p n : ℕ}
    (w : Context × FFVec p (n + 1)) :
    lastSplitEquiv Context p n w =
      ((w.1, fun j ↦ w.2 j.castSucc), w.2 (Fin.last n)) := by
  rfl

/-- Pushforward expectation identity for a finite distribution. -/
theorem sum_map_mass_mul'
    {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : FinDist A) (f : A → B) (g : B → ℝ) :
    ∑ b, (P.map f).mass b * g b = ∑ a, P.mass a * g (f a) := by
  simp only [map_mass, Finset.sum_mul]
  calc
    (∑ b, ∑ a with f a = b, P.mass a * g b) =
        ∑ b, ∑ a with f a = b, P.mass a * g (f a) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a, P.mass a * g (f a) := by
      simpa using! (Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset A) (Finset.univ : Finset B) f
        (fun a ↦ P.mass a * g (f a)))

/-- Splitting the last entry sends a context times a uniform tuple to the
corresponding three-factor product. -/
theorem map_context_uniform_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (C : FinDist Context) :
    (C.prod (FinDist.uniform (FFVec p (n + 1)))).map
        (lastSplitEquiv Context p n) =
      (C.prod (FinDist.uniform (FFVec p n))).prod
        (FinDist.uniform (ZMod p)) := by
  ext q
  let e := lastSplitEquiv Context p n
  let w := e.symm q
  have hw : e w = q := e.apply_symm_apply q
  rw [← hw, map_equiv_mass]
  simp only [prod_mass, uniform_mass, fintypeCard_ffVec, ZMod.card,
    e, lastSplitEquiv_apply]
  rw [pow_succ]
  push_cast
  field_simp [NeZero.ne p]

/-- The prefix marginal obtained after the last-coordinate split is the
pushforward by the literal prefix map. -/
theorem fst_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1))) :
    (P.map (lastSplitEquiv Context p n)).fst =
      P.map (fun w ↦ (w.1, fun j ↦ w.2 j.castSucc)) := by
  rw [fst, map_map]
  apply congrArg (fun f ↦ P.map f)
  funext w
  rfl

/-- Splitting off tuple entries does not alter the original context
marginal. -/
theorem fst_fst_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1))) :
    ((P.map (lastSplitEquiv Context p n)).fst).fst = P.fst := by
  rw [fst_map_lastSplit, fst, map_map]
  apply congrArg (fun f ↦ P.map f)
  funext w
  rfl

@[simp]
theorem tuplePrefix_castSucc {p n : ℕ}
    (i : Fin n) (z : FFVec p (n + 1)) :
    tuplePrefix i.castSucc z =
      tuplePrefix i (fun j ↦ z j.castSucc) := by
  funext j
  rfl

@[simp]
theorem tuplePrefix_last {p n : ℕ} (z : FFVec p (n + 1)) :
    tuplePrefix (Fin.last n) z = fun j ↦ z j.castSucc := by
  funext j
  rfl

/-- A law on `Context × (Fin 0 → A)` is completely determined by its
context marginal. -/
theorem eq_fst_prod_uniform_finZero
    {Context A : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype A] [Nonempty A]
    (P : FinDist (Context × (Fin 0 → A))) :
    P = P.fst.prod (FinDist.uniform (Fin 0 → A)) := by
  ext w
  have hmass := P.fst_mass w.1
  have hcard : Fintype.card (Fin 0 → A) = 1 := by simp
  have hsum : (∑ u : Fin 0 → A, P.mass (w.1, u)) =
      P.mass w := by
    classical
    simp [Subsingleton.elim (α := Fin 0 → A) _ w.2]
  simp only [prod_mass, uniform_mass, hcard, Nat.cast_one, inv_one, mul_one]
  exact (hmass.trans hsum).symm

/-- Selecting one symbol in every context is the same as summing the
corresponding indicator over the whole joint law. -/
theorem sum_selected_eq_sum_indicator
    {Context : Type*} [Fintype Context]
    {p : ℕ} [NeZero p]
    (Q : FinDist (Context × ZMod p))
    (predictor : Context → ZMod p) :
    (∑ c, Q.mass (c, predictor c)) =
      ∑ q, Q.mass q *
        (if predictor q.1 = q.2 then (1 : ℝ) else 0) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _hc
  classical
  simp

/-- The selected-mass expression after a last-coordinate split, pulled
back to the original tuple. -/
theorem sum_selected_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1)))
    (predictor : Context × FFVec p n → ZMod p) :
    (∑ c, (P.map (lastSplitEquiv Context p n)).mass
        (c, predictor c)) =
      ∑ w, P.mass w *
        (if predictor (w.1, fun j ↦ w.2 j.castSucc) =
            w.2 (Fin.last n) then (1 : ℝ) else 0) := by
  rw [sum_selected_eq_sum_indicator]
  exact sum_map_mass_mul' P (lastSplitEquiv Context p n)
    (fun q ↦ if predictor q.1 = q.2 then (1 : ℝ) else 0)

/-- Pull a success event on a prefix marginal back to the original
tuple. -/
theorem sum_prefixEvent_map_lastSplit
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p n : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p (n + 1)))
    (i : Fin n) (predictor : Context × FFVec p i.val → ZMod p) :
    (∑ u, (P.map (lastSplitEquiv Context p n)).fst.mass u *
        (if predictor (u.1, tuplePrefix i u.2) = u.2 i
          then (1 : ℝ) else 0)) =
      ∑ w, P.mass w *
        (if predictor (w.1, tuplePrefix i.castSucc w.2) =
            w.2 i.castSucc then (1 : ℝ) else 0) := by
  rw [fst_map_lastSplit]
  have h := sum_map_mass_mul' P
    (fun w ↦ (w.1, fun j ↦ w.2 j.castSucc))
    (fun u ↦ if predictor (u.1, tuplePrefix i u.2) = u.2 i
      then (1 : ℝ) else 0)
  simpa only [tuplePrefix_castSucc] using! h

/-- A finite chain-rule form of the hybrid argument.  If a tuple remains
far from uniform after conditioning on an arbitrary context, then one
coordinate is predictably biased from the context and all preceding
coordinates. -/
theorem exists_sequential_predictor_of_tv_gt
    {Context : Type*} [Fintype Context] [DecidableEq Context]
    {p r : ℕ} [Fact p.Prime]
    (P : FinDist (Context × FFVec p r))
    (δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hfar : δ < P.tv (P.fst.prod (FinDist.uniform (FFVec p r)))) :
    ∃ i : Fin r,
      ∃ predictor : Context × FFVec p i.val → ZMod p,
        1 / (p : ℝ) + δ / ((r : ℝ) * p) <
          ∑ w, P.mass w *
            (if predictor (w.1, tuplePrefix i w.2) = w.2 i
              then (1 : ℝ) else 0) := by
  induction r generalizing δ with
  | zero => omega
  | succ n ih =>
      let e := lastSplitEquiv Context p n
      let Q : FinDist ((Context × FFVec p n) × ZMod p) := P.map e
      let U := FinDist.uniform (ZMod p)
      let prefixUniform := P.fst.prod (FinDist.uniform (FFVec p n))
      have hfarQ : δ < Q.tv (prefixUniform.prod U) := by
        dsimp only [Q, e, prefixUniform, U]
        rw [← map_context_uniform_lastSplit P.fst]
        rw [tv_map_equiv]
        exact hfar
      have htriangle : Q.tv (prefixUniform.prod U) ≤
          Q.tv (Q.fst.prod U) + Q.fst.tv prefixUniform := by
        have h := tv_triangle Q (Q.fst.prod U) (prefixUniform.prod U)
        rwa [tv_prod_right] at h
      by_cases hn : n = 0
      · subst n
        have hprefixZero : Q.fst.tv prefixUniform = 0 := by
          have hQ := eq_fst_prod_uniform_finZero Q.fst
          have hff := fst_fst_map_lastSplit P
          change Q.fst.fst = P.fst at hff
          dsimp only [prefixUniform]
          rw [hQ, hff, tv_self]
        have hlast : δ < Q.tv (Q.fst.prod U) := by
          linarith
        obtain ⟨predictor, hpredictor⟩ :=
          exists_predictor_of_tv_gt Q δ hlast
        refine ⟨Fin.last 0, predictor, ?_⟩
        rw [show ((0 + 1 : ℕ) : ℝ) = 1 by norm_num]
        simp only [one_mul]
        calc
          1 / (p : ℝ) + δ / p <
              ∑ c, (P.map (lastSplitEquiv Context p 0)).mass
                (c, predictor c) := by
            simpa only [Q, e] using! hpredictor
          _ = ∑ w, P.mass w *
              (if predictor (w.1, tuplePrefix (Fin.last 0) w.2) =
                w.2 (Fin.last 0) then (1 : ℝ) else 0) := by
            simpa only [tuplePrefix_last] using!
              (sum_selected_map_lastSplit P predictor)
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        by_cases hlast : δ / (n + 1 : ℝ) < Q.tv (Q.fst.prod U)
        · obtain ⟨predictor, hpredictor⟩ :=
            exists_predictor_of_tv_gt Q (δ / (n + 1 : ℝ)) hlast
          refine ⟨Fin.last n, predictor, ?_⟩
          simp only [Nat.cast_add, Nat.cast_one]
          have hconst :
              1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) + (δ / (n + 1 : ℝ)) / p := by
            field_simp [NeZero.ne p]
          calc
            1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) + (δ / (n + 1 : ℝ)) / p := hconst
            _ < ∑ c, (P.map (lastSplitEquiv Context p n)).mass
                  (c, predictor c) := by
              simpa only [Q, e] using! hpredictor
            _ = ∑ w, P.mass w *
                (if predictor (w.1, tuplePrefix (Fin.last n) w.2) =
                  w.2 (Fin.last n) then (1 : ℝ) else 0) := by
              simpa only [tuplePrefix_last] using!
                (sum_selected_map_lastSplit P predictor)
        · have hlastLe : Q.tv (Q.fst.prod U) ≤
              δ / (n + 1 : ℝ) := le_of_not_gt hlast
          have hsplit : δ / (n + 1 : ℝ) +
              δ * n / (n + 1 : ℝ) = δ := by
            have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
            field_simp
            ring
          have hprefix : δ * n / (n + 1 : ℝ) <
              Q.fst.tv prefixUniform := by
            nlinarith
          have hδprefix : 0 < δ * n / (n + 1 : ℝ) := by positivity
          have hQfst : Q.fst.fst = P.fst := by
            exact fst_fst_map_lastSplit P
          have hprefix' : δ * n / (n + 1 : ℝ) <
              Q.fst.tv (Q.fst.fst.prod
                (FinDist.uniform (FFVec p n))) := by
            rwa [hQfst]
          obtain ⟨i, predictor, hpredictor⟩ :=
            ih Q.fst (δ * n / (n + 1 : ℝ)) hnpos hδprefix hprefix'
          refine ⟨i.castSucc, predictor, ?_⟩
          simp only [Nat.cast_add, Nat.cast_one]
          have hadv :
              (δ * n / (n + 1 : ℝ)) / ((n : ℝ) * p) =
                δ / ((n + 1 : ℝ) * p) := by
            field_simp [NeZero.ne p, Nat.ne_of_gt hnpos]
          calc
            1 / (p : ℝ) + δ / ((n + 1 : ℝ) * p) =
                1 / (p : ℝ) +
                  (δ * n / (n + 1 : ℝ)) / ((n : ℝ) * p) := by
              rw [hadv]
            _ < ∑ u, Q.fst.mass u *
                (if predictor (u.1, tuplePrefix i u.2) = u.2 i
                  then (1 : ℝ) else 0) := hpredictor
            _ = ∑ w, P.mass w *
                (if predictor (w.1, tuplePrefix i.castSucc w.2) =
                  w.2 i.castSucc then (1 : ℝ) else 0) := by
              simpa only [Q, e] using!
                (sum_prefixEvent_map_lastSplit P i predictor)

end FinDist

end Erdos788
