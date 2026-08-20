/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Optimally sized topological cliques from a local routing reservoir. -/

import ErdosProblems.Erdos717.SubsetSampling
import Mathlib.Algebra.Order.Floor.Div

open Function Set
open SimpleGraph

namespace Erdos717

/-- Exact-size version of the reservoir argument.  The relation
`R^(a-1) s ≤ Q` supplies `s` branch vertices, while `12s²+2R ≤ LR`
is precisely the (sampled) missing-pair routing budget. -/
theorem containsCliqueSubdivision_of_local_reservoir_size
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (Q L R a s : ℕ)
    (hUcard : Q ≤ U.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (hR : 1 ≤ R) (ha : 1 ≤ a) (hind : IndepBoundOn G U a)
    (hs : 2 ≤ s) (hsize : R ^ (a - 1) * s ≤ Q)
    (hroute : 12 * (s * s) + 2 * R ≤ L * R) :
    Erdos718.ContainsCliqueSubdivision G s := by
  classical
  have haeq : a - 1 + 1 = a := by omega
  obtain ⟨T, hTU, hUT, hmissingT⟩ :=
    exists_nearly_complete_subset_aux G U R (a - 1) hR (by
      simpa only [haeq] using hind)
  have hpowPos : 0 < R ^ (a - 1) := pow_pos (by omega) _
  have hsT : s ≤ T.card := by
    have hscaled : R ^ (a - 1) * s ≤ R ^ (a - 1) * T.card :=
      hsize.trans (hUcard.trans hUT)
    exact Nat.le_of_mul_le_mul_left hscaled hpowPos
  obtain ⟨S, hST, hScard, hmissingS⟩ :=
    exists_subset_missingOrdered_density G T R s hs hsT hmissingT
  let enum : S ≃ Fin s := S.equivFinOfCardEq hScard
  let branch : Fin s ↪ V := enum.symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩
  have hbranch (i : Fin s) : branch i ∈ S := (enum.symm i).property
  have hrange : Set.range branch ⊆ (U : Set V) := by
    rintro _ ⟨i, rfl⟩
    exact hTU (hST (hbranch i))
  let missing := Finset.univ.filter fun e : Erdos718.CliqueEdge s =>
    ¬G.Adj (branch e.1.1) (branch e.1.2)
  have hmissingLe : missing.card ≤ (missingOrderedPairs G S).card := by
    apply missing_cliqueEdge_card_le_ordered G branch S
    rintro _ ⟨i, rfl⟩
    exact hbranch i
  have hscaledMissing : R * (6 * missing.card + 2) ≤ R * L := by
    calc
      R * (6 * missing.card + 2) = 6 * (R * missing.card) + 2 * R := by ring
      _ ≤ 6 * (R * (missingOrderedPairs G S).card) + 2 * R := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left R hmissingLe)) _
      _ ≤ 12 * (s * s) + 2 * R := by omega
      _ ≤ L * R := hroute
      _ = R * L := by ring
  apply hreservoir branch hrange
  exact Nat.le_of_mul_le_mul_left hscaledMissing (by omega)

/-- Optimal-size high-density branch after neighbourhood-pattern thinning. -/
theorem containsCliqueSubdivision_of_patterned_reservoir_size
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I W U₀ : Finset V) (X0 L R b Q s : ℕ)
    (hIP : I ⊆ P) (hWP : W ⊆ P)
    (hIind : G.IsIndepSet I) (hImax : IndepBoundOn G P I.card)
    (hIW : Disjoint I W)
    (hdegree : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b)
    (hU₀W : U₀ ⊆ W) (hU₀card : X0 / 5 ≤ U₀.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U₀ : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (hb : 1 ≤ b) (hR : 1 ≤ R)
    (hQbase : Q ≤ X0 / 5)
    (hpatterns : I.card.choose b * Q ≤ U₀.card)
    (hs : 2 ≤ s) (hsize : R ^ (b - 1) * s ≤ Q)
    (hroute : 12 * (s * s) + 2 * R ≤ L * R) :
    Erdos718.ContainsCliqueSubdivision G s := by
  classical
  obtain ⟨U, hUU₀, hUcard, hlocal⟩ :=
    exists_exact_pattern_subset G P I W U₀ X0 b Q hIP hWP hIind hImax
      hIW hdegree hU₀W hU₀card hQbase hpatterns
  have hreservoirU : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r := by
    intro r branch hrange hmissing
    exact hreservoir branch (hrange.trans (by exact_mod_cast hUU₀)) hmissing
  apply containsCliqueSubdivision_of_local_reservoir_size
    G U Q L R b s (by simp [hUcard]) hreservoirU hR hb hlocal hs hsize hroute

/-- Contrapositive optimization of the exact-size reservoir theorem.  If a
reservoir with local independence bound `a` does not contain `TK_k`, then its
size and route budget obey the displayed root-type polynomial inequality. -/
theorem local_reservoir_order_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (Q L a k : ℕ)
    (hUcard : Q ≤ U.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (ha : 1 ≤ a) (hind : IndepBoundOn G U a)
    (hL : 5 ≤ L) (hk : 2 ≤ k)
    (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    Q < k ∨ L ^ (a - 1) * Q < 38 ^ (a - 1) * k ^ (2 * a - 1) := by
  classical
  by_cases hQk : Q < k
  · exact Or.inl hQk
  right
  have hkQ : k ≤ Q := Nat.le_of_not_gt hQk
  by_cases hlarge : 12 * (k * k) + 2 ≤ L
  · exfalso
    apply hnot
    apply containsCliqueSubdivision_of_local_reservoir_size
      G U Q L 1 a k hUcard hreservoir (by simp) ha hind hk
    · simpa using hkQ
    · simpa using hlarge
  · have hLupper : L ≤ 13 * (k * k) := by
      have : L < 12 * (k * k) + 2 := Nat.lt_of_not_ge hlarge
      nlinarith
    let R := (24 * (k * k)) ⌈/⌉ L
    have hcover : 24 * (k * k) ≤ L * R := by
      exact (ceilDiv_le_iff_le_mul (by omega : 0 < L)).mp le_rfl
    have hR : 1 ≤ R := by
      by_contra hzero
      have hReq : R = 0 := by omega
      rw [hReq] at hcover
      nlinarith
    have hRupper : R ≤ 5 * (k * k) := by
      rw [ceilDiv_le_iff_le_mul (by omega : 0 < L)]
      nlinarith
    have hroute : 12 * (k * k) + 2 * R ≤ L * R := by
      calc
        12 * (k * k) + 2 * R ≤ 24 * (k * k) := by nlinarith
        _ ≤ L * R := hcover
    have hsizeFail : Q < R ^ (a - 1) * k := by
      by_contra hsize
      apply hnot
      apply containsCliqueSubdivision_of_local_reservoir_size
        G U Q L R a k hUcard hreservoir hR ha hind hk
      · exact Nat.le_of_not_gt hsize
      · exact hroute
    have hLRupper : L * R ≤ 37 * (k * k) := by
      have hceil : L * R ≤ 24 * (k * k) + L - 1 := by
        dsimp only [R, Nat.ceilDiv_eq_add_pred_div]
        exact Nat.mul_div_le (24 * (k * k) + L - 1) L
      calc
        L * R ≤ 24 * (k * k) + L - 1 := hceil
        _ ≤ 24 * (k * k) + L := Nat.sub_le _ _
        _ ≤ 37 * (k * k) := by nlinarith
    have hmulStrict : L ^ (a - 1) * Q <
        (L * R) ^ (a - 1) * k := by
      calc
        L ^ (a - 1) * Q < L ^ (a - 1) * (R ^ (a - 1) * k) := by
          exact Nat.mul_lt_mul_of_pos_left hsizeFail (pow_pos (by omega) _)
        _ = (L * R) ^ (a - 1) * k := by rw [Nat.mul_pow]; ring
    calc
      L ^ (a - 1) * Q < (L * R) ^ (a - 1) * k := hmulStrict
      _ ≤ (37 * (k * k)) ^ (a - 1) * k := by
        exact Nat.mul_le_mul_right k (Nat.pow_le_pow_left hLRupper (a - 1))
      _ ≤ (38 * (k * k)) ^ (a - 1) * k := by
        apply Nat.mul_le_mul_right k
        exact Nat.pow_le_pow_left (by nlinarith) (a - 1)
      _ = 38 ^ (a - 1) * k ^ (2 * a - 1) := by
        rw [Nat.mul_pow, mul_assoc]
        congr 1
        rw [Nat.mul_pow, ← pow_add]
        conv_lhs => rhs; rw [← pow_one k]
        rw [← pow_add]
        congr 1
        omega

/-- The polynomial order inequality after neighbourhood-pattern thinning. -/
theorem patterned_reservoir_order_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P I W U₀ : Finset V) (X0 L b Q k : ℕ)
    (hIP : I ⊆ P) (hWP : W ⊆ P)
    (hIind : G.IsIndepSet I) (hImax : IndepBoundOn G P I.card)
    (hIW : Disjoint I W)
    (hdegree : ∀ v ∈ W, (G.neighborFinset v ∩ I).card ≤ b)
    (hU₀W : U₀ ⊆ W) (hU₀card : X0 / 5 ≤ U₀.card)
    (hreservoir : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U₀ : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r)
    (hb : 1 ≤ b) (hQbase : Q ≤ X0 / 5)
    (hpatterns : I.card.choose b * Q ≤ U₀.card)
    (hL : 5 ≤ L) (hk : 2 ≤ k)
    (hnot : ¬Erdos718.ContainsCliqueSubdivision G k) :
    Q < k ∨ L ^ (b - 1) * Q < 38 ^ (b - 1) * k ^ (2 * b - 1) := by
  classical
  obtain ⟨U, hUU₀, hUcard, hlocal⟩ :=
    exists_exact_pattern_subset G P I W U₀ X0 b Q hIP hWP hIind hImax
      hIW hdegree hU₀W hU₀card hQbase hpatterns
  have hreservoirU : ∀ {r : ℕ} (branch : Fin r ↪ V),
      Set.range branch ⊆ (U : Set V) →
      6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
        ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
      Erdos718.ContainsCliqueSubdivision G r := by
    intro r branch hrange hmissing
    exact hreservoir branch (hrange.trans (by exact_mod_cast hUU₀)) hmissing
  exact local_reservoir_order_inequality G U Q L b k
    (by simp [hUcard]) hreservoirU hb hlocal hL hk hnot

end Erdos717
