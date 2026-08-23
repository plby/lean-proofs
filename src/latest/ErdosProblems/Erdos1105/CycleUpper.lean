import ErdosProblems.Erdos1105.ComponentTriangles
import ErdosProblems.Erdos1105.CycleUpperReduction

namespace Erdos1105

open SimpleGraph Asymptotics Filter

noncomputable def componentRepresentative {V : Type*} (R : SimpleGraph V) :
    R.ConnectedComponent ↪ V where
  toFun := fun B ↦ B.out
  inj' := by
    intro B D h
    exact B.out_eq.symm.trans ((congrArg R.connectedComponentMk h).trans D.out_eq)

noncomputable def componentQuotientColor {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V) :
    (⊤ : SimpleGraph R.ConnectedComponent).edgeSet → C :=
  c ∘ (completeCopy ⊤ (componentRepresentative R)).mapEdgeSet

lemma extend_componentQuotient_pair {V C : Type*}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (R : SimpleGraph V)
    (B D : R.ConnectedComponent) (hBD : B ≠ D) :
    extendColor c s(B.out, D.out) = some (componentQuotientColor c R ⟨s(B, D), hBD⟩) :=
  extendColor_edge c ((completeCopy ⊤ (componentRepresentative R)).mapEdgeSet ⟨s(B, D), hBD⟩)

/-- The high-private-degree structural decomposition gives the sharp
linear cycle upper bound for every nonempty host. -/
theorem private_coloring_upper_bound {V C : Type*} [Fintype V] [Nonempty V] [Fintype C] {n : ℕ}
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (hH : ∀ f : (cycleGraph (n + 4)).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : Set.InjOn (extendColor c) R.edgeSet)
    (howned : ∀ e : R.edgeSet, ∃ w, PrivateAt c w
      (c ⟨e.val, edgeSet_mono (show R ≤ ⊤ from le_top) e.property⟩))
    (hpalette : ∀ i, (∃ v, PrivateAt c v i) → ∃ e : R.edgeSet, extendColor c e.val = some i)
    (hnew : ∀ v, 2 ≤ (privateColors c v).card)
    (hsum : ∀ x y, x ≠ y → n + 3 ≤ (privateColors c x).card + (privateColors c y).card) :
    (Fintype.card C : ℝ) ≤
      (((n + 3 : ℕ) - (1 : ℝ)) / 2 + 1 / (n + 3 : ℕ)) * Fintype.card V - 1 := by
  classical
  let raw := componentQuotientColor c R
  let D := Set.range raw
  let d : (⊤ : SimpleGraph R.ConnectedComponent).edgeSet → D := fun e ↦ ⟨raw e, ⟨e, rfl⟩⟩
  have hd : Function.Surjective d := by
    rintro ⟨col, e, rfl⟩
    exact ⟨e, rfl⟩
  have hsize (B : R.ConnectedComponent) : Fintype.card {v // R.connectedComponentMk v = B} ≤ n + 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact private_component_card_le c hc hH R hR howned hpalette hnew hsum B
  have hcross : ∀ a b (hab : a ≠ b) (hne : R.connectedComponentMk a ≠ R.connectedComponentMk b),
      c ⟨s(a, b), hab⟩ = (d ⟨s(R.connectedComponentMk a, R.connectedComponentMk b), hne⟩).val := by
    intro a b hab hne
    let A := R.connectedComponentMk a
    let B := R.connectedComponentMk b
    let := Fintype.ofFinite A
    let := Fintype.ofFinite B
    have hcol := private_component_cross_monochromatic c hc hH R hR howned hpalette hnew hsum
      A B hne ⟨a, rfl⟩ ⟨A.out, A.out_eq⟩ ⟨b, rfl⟩ ⟨B.out, B.out_eq⟩
    apply Option.some.inj
    calc
      some (c ⟨s(a, b), hab⟩) = extendColor c s(a, b) := (extendColor_edge c _).symm
      _ = extendColor c s(A.out, B.out) := hcol
      _ = some (raw ⟨s(A, B), hne⟩) := extend_componentQuotient_pair c R A B hne
  have htri : NoRainbowTriangle (extendColor d) := by
    intro A B E hAB hBE hAE
    let := Fintype.ofFinite A
    let := Fintype.ofFinite B
    let := Fintype.ofFinite E
    have ht := private_component_triangle_colors c hc hH R hR howned hpalette hnew hsum
      A B E hAB hBE hAE.symm ⟨A.out, A.out_eq⟩ ⟨B.out, B.out_eq⟩ ⟨E.out, E.out_eq⟩
    have hAB' := extend_componentQuotient_pair c R A B hAB
    have hBE' := extend_componentQuotient_pair c R B E hBE
    have hEA' : extendColor c s(E.out, A.out) = some (raw ⟨s(A, E), hAE⟩) := by
      rw [Sym2.eq_swap]
      exact extend_componentQuotient_pair c R A E hAE
    change extendColor c s(A.out, B.out) = extendColor c s(B.out, E.out) ∨
      extendColor c s(B.out, E.out) = extendColor c s(E.out, A.out) ∨
      extendColor c s(E.out, A.out) = extendColor c s(A.out, B.out) at ht
    rw [hAB', hBE', hEA'] at ht
    simp only [Option.some.injEq] at ht
    rw [show extendColor d s(A, B) = some (d ⟨s(A, B), hAB⟩) from
        extendColor_edge d ⟨s(A, B), hAB⟩,
      show extendColor d s(B, E) = some (d ⟨s(B, E), hBE⟩) from
        extendColor_edge d ⟨s(B, E), hBE⟩,
      show extendColor d s(A, E) = some (d ⟨s(A, E), hAE⟩) from
        extendColor_edge d ⟨s(A, E), hAE⟩]
    simp only [Option.some.injEq]
    rcases ht with ht | ht | ht
    · exact Or.inl (Subtype.ext ht)
    · exact Or.inr (Or.inr (Subtype.ext ht))
    · exact Or.inr (Or.inl (Subtype.ext ht.symm))
  exact weak_blocks_upper_bound (n + 3) (by omega) R.connectedComponentMk
    (fun B ↦ B.exists_rep) hsize c hc d hd Subtype.val hcross htri

/-- The previously isolated high-private-color input is now proved. -/
theorem high_private_cycle_bound (k : ℕ) (hk : 4 ≤ k) : HighPrivateCycleBound k := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
  intro n q c hc hH hhigh
  cases n with
  | zero =>
    have hq := Fintype.card_le_of_surjective c hc
    have hq0 : q = 0 := by simpa using hq
    simp [hq0]
  | succ n =>
    obtain ⟨R, hR, howned, _, hpalette⟩ := exists_private_representative c hc
    have hnew (v : Fin (n + 1)) : 2 ≤ (privateColors c v).card := by
      have hv := hhigh v
      have hlt : (1 : ℝ) < (privateColors c v).card := by
        push_cast at hv
        linarith [Nat.cast_nonneg m (α := ℝ)]
      exact_mod_cast hlt
    have hsum (u v : Fin (n + 1)) (_ : u ≠ v) :
        m + 3 ≤ (privateColors c u).card + (privateColors c v).card := by
      have hu := hhigh u
      have hv := hhigh v
      have hlt : (m + 2 : ℕ) < (privateColors c u).card + (privateColors c v).card := by
        have hltR : (m + 2 : ℕ) < ((privateColors c u).card : ℝ) + (privateColors c v).card := by
          push_cast at hu hv ⊢
          linarith
        exact_mod_cast hltR
      omega
    have hbound := private_coloring_upper_bound c hc hH R hR howned hpalette hnew hsum
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat] at hbound ⊢
    have heq : (m : ℝ) + 4 - 2 = (m : ℝ) + 3 - 1 := by ring
    have heq' : (m : ℝ) + 4 - 1 = (m : ℝ) + 3 := by ring
    rw [heq, heq']
    linarith

/-- The affirmative cycle asymptotic in full generality. -/
theorem cycle_asymptotic (k : ℕ) (hk : 3 ≤ k) :
    ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ))) := by
  by_cases hk3 : k = 3
  · subst k
    rw [isBigO_one_nat_atTop_iff]
    refine ⟨1, fun n ↦ ?_⟩
    rw [antiRamseyNum_cycleGraph_three]
    cases n <;> norm_num
  · exact cycle_asymptotic_of_high_private_bound k hk (high_private_cycle_bound k (by omega))

#print axioms high_private_cycle_bound
#print axioms cycle_asymptotic

end Erdos1105
