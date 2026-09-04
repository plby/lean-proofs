import Mathlib
import ErdosProblems.Erdos336.IntervalLatticeExtension
import ErdosProblems.Erdos336.TwoGeneratorLShape

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Sharp cardinal bound from an aggregate cyclic-interval cover
-/

namespace Erdos336

/-- Every target has a representation `j a + k d`, where `j≤H` and
`0≤k≤Vj`; this is the aggregate form of weak coverage by an interval
`{a,a+d,...,a+Vd}`. -/
def IntervalAggregateCover {G : Type*} [AddCommGroup G]
    (f : IntPair →+ G) (V H : ℕ) : Prop :=
  ∀ g : G, ∃ j k : ℕ, j ≤ H ∧ k ≤ V * j ∧
    f ((j : ℤ), (k : ℤ)) = g

private theorem intervalAggregate_surjective
    {G : Type*} [AddCommGroup G]
    (f : IntPair →+ G) {V H : ℕ}
    (hcover : IntervalAggregateCover f V H) :
    Function.Surjective f := by
  intro g
  obtain ⟨j, k, -, -, hjk⟩ := hcover g
  exact ⟨((j : ℤ), (k : ℤ)), hjk⟩

private theorem quotient_twoGenLabel
    (L : AddSubgroup IntPair) (x y : ℕ) :
    twoGenLabel
      ((QuotientAddGroup.mk' L) (1, 0))
      ((QuotientAddGroup.mk' L) (0, 1)) (x, y) =
      (QuotientAddGroup.mk' L) ((x : ℤ), (y : ℤ)) := by
  simp only [twoGenLabel]
  rw [← (QuotientAddGroup.mk' L).map_nsmul x (1, 0),
    ← (QuotientAddGroup.mk' L).map_nsmul y (0, 1), ← map_add]
  apply congrArg (QuotientAddGroup.mk' L)
  apply Prod.ext <;> simp

/-- The determinant-`V` extension turns an aggregate interval cover of height
`H` into an ordinary two-generator cover of diameter at most `V(H+1)`. -/
theorem intervalExtension_twoGenerator_cover
    {G : Type*} [AddCommGroup G]
    (f : IntPair →+ G) {V H : ℕ} (hV : 0 < V)
    (hcover : IntervalAggregateCover f V H) :
    let L' := stretchedKernel f V
    let E := IntervalLatticeExtension f V
    ∀ z : E, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ V * (H + 1) ∧
      twoGenLabel
        ((QuotientAddGroup.mk' L') (1, 0))
        ((QuotientAddGroup.mk' L') (0, 1)) p = z := by
  dsimp only
  intro z
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective z
  let s : ℤ := u.1 + u.2
  let t : ℤ := s % (V : ℤ)
  let T : ℕ := t.toNat
  let j : ℤ := s / (V : ℤ)
  have hVZ : (V : ℤ) ≠ 0 := by omega
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Int.emod_nonneg _ hVZ
  have htV : t < (V : ℤ) := by
    dsimp [t]
    simpa using Int.emod_lt s hVZ
  have hTcast : (T : ℤ) = t := by
    exact Int.toNat_of_nonneg ht0
  have hTV : T < V := by omega
  have hdecomp : (V : ℤ) * j + t = s := by
    dsimp [j, t]
    nlinarith [Int.ediv_mul_add_emod s (V : ℤ)]
  let g := f (j, u.2)
  obtain ⟨J, K, hJ, hK, hJK⟩ := hcover g
  let X : ℕ := T + V * J - K
  have hK' : K ≤ T + V * J := le_trans hK (Nat.le_add_left _ _)
  have hXK : X + K = T + V * J := by
    dsimp [X]
    omega
  refine ⟨(X, K), ?_, ?_⟩
  · rw [hXK]
    nlinarith
  · rw [quotient_twoGenLabel]
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    let q : IntPair := ((J : ℤ) - j, (K : ℤ) - u.2)
    have hqker : q ∈ f.ker := by
      change f q = 0
      have hqeq : q = ((J : ℤ), (K : ℤ)) - (j, u.2) := by
        apply Prod.ext <;> rfl
      rw [hqeq, map_sub, hJK]
      exact sub_self _
    refine ⟨q, hqker, ?_⟩
    apply Prod.ext
    · dsimp [q, intervalStretchHom, X]
      rw [Int.natCast_sub hK']
      push_cast
      dsimp [s] at hdecomp
      nlinarith
    · rfl

/-- Aggregate interval coverage has the sharp one-third cardinal coefficient:
`3V|G| ≤ (V(H+1)+2)²`. -/
theorem intervalAggregate_card_bound
    {G : Type*} [AddCommGroup G] [Finite G]
    (f : IntPair →+ G) {V H : ℕ} (hV : 0 < V)
    (hcover : IntervalAggregateCover f V H) :
    3 * (V * Nat.card G) ≤ (V * (H + 1) + 2) ^ 2 := by
  classical
  have hf := intervalAggregate_surjective f hcover
  let L' := stretchedKernel f V
  let E := IntervalLatticeExtension f V
  have hcard := card_intervalLatticeExtension f hV hf
  have hindex : L'.index ≠ 0 := by
    rw [AddSubgroup.index_eq_card, hcard]
    exact Nat.mul_ne_zero (Nat.ne_of_gt hV) Nat.card_pos.ne'
  let : Fintype E := AddSubgroup.fintypeOfIndexNeZero hindex
  let e₁ : E := (QuotientAddGroup.mk' L') (1, 0)
  let e₂ : E := (QuotientAddGroup.mk' L') (0, 1)
  have htwo : ∀ z : E, ∃ p : ℕ × ℕ,
      p.1 + p.2 ≤ V * (H + 1) ∧ twoGenLabel e₁ e₂ p = z := by
    simpa [E, L', e₁, e₂] using intervalExtension_twoGenerator_cover f hV hcover
  have hbound := twoGenerator_card_le_third e₁ e₂ htwo
  have hcardF : Fintype.card E = V * Nat.card G := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  simpa [hcardF] using hbound

end Erdos336
