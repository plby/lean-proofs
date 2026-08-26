-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import Mathlib
import ErdosProblems.Erdos1177.GSn
import ErdosProblems.Erdos1177.EHGirthChromatic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The chromatic lower bound for `GS_n(κ)` (Erdős–Galvin–Hajnal, Lemma 8.3(B))

This file proves that the generalized Specker graph `GS_n(κ)` of
`ErdosProblems.Erdos1177.GSn` is **not `θ`-colourable for any `θ < κ`** (`ℵ₀ < κ`), i.e.
`χ(GS_n(κ)) = κ` (with the cardinality bound `card_le`).

The chromatic lower bound is the Erdős–Rado transfinite cofinal-"peeling"
argument, generalizing the `n = 1` base case `ER60.not_colorableBy`.  We reuse
the graph-independent stabilization tower `EHG.stab` and its helpers from
`ErdosProblems.Erdos1177.EHGirthChromatic` (they operate on colourings of `ℕ → Pt κ` and
are unaware of the edge relation); the only `GS_n`-specific ingredient is the
**extraction**: from the fully stabilized tower we read off two `L`-tuples that
interleave as a `GS_n` edge and share the stabilized colour, contradicting
properness.

`GSn.Vtx n κ` and `EHG.Vtx (L n) κ` are definitionally equal, so the tower
machinery instantiated at `k = L n` applies verbatim.
-/

open Cardinal

namespace Erdos1177
namespace GSn

open ER60 (Pt Cofinal cofinal_fiber cofinal_Ioi cofinal_univ)

universe u

variable {κ : Cardinal.{u}} {n : ℕ} {θ : Cardinal.{u}}

/-! ### Initial-segment reduction -/

/-- `IsEdge` is preserved by applying a strictly monotone map coordinatewise. -/
theorem isEdge_map {μ : Cardinal.{u}} (e : Pt μ ↪o Pt κ) {u v : Fin (L n) → Pt μ}
    (h : IsEdge u v) : IsEdge (fun i => e (u i)) (fun i => e (v i)) := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun t ht => e.strictMono (h1 t ht), fun t ht => e.strictMono (h2 t ht)⟩

/-- **Colourability transfers down initial segments.**  If `μ ≤ κ` and
`graph n κ` is `θ`-colourable, so is `graph n μ`. -/
theorem colorableBy_of_le {μ : Cardinal.{u}} (hμκ : μ ≤ κ)
    (h : (SimpleGraph.toHG (graph n κ)).ColorableBy θ) :
    (SimpleGraph.toHG (graph n μ)).ColorableBy θ := by
  obtain ⟨e, -⟩ : ∃ _ : Pt μ ↪o Pt κ, True :=
    ⟨Classical.choice (ER60.exists_pt_orderEmbedding hμκ), trivial⟩
  obtain ⟨c, hc⟩ := h
  have hadjκ : ∀ a b : Vtx n κ, (graph n κ).Adj a b → c a ≠ c b := by
    intro a b hab
    exact (toHG_proper_iff _ c).1 hc a b hab
  refine ⟨fun a => c ⟨fun i => e (a.1 i), e.strictMono.comp a.2⟩, ?_⟩
  rw [toHG_proper_iff]
  intro x y hxy
  refine hadjκ ⟨fun i => e (x.1 i), e.strictMono.comp x.2⟩
    ⟨fun i => e (y.1 i), e.strictMono.comp y.2⟩ ?_
  rcases hxy with h | h
  · exact Or.inl (isEdge_map e h)
  · exact Or.inr (isEdge_map e h)

/-! ### The chromatic lower bound at a regular cardinal (peeling + extraction) -/

/-
**Single-tuple run.**  Place `r` consecutive coordinates `q, …, q+r-1` of one
tuple, each above the running bound `B`, preserving the stabilized colour and
strict monotonicity.  Proved by induction on `r` with `EHG.exists_next_star`.
-/
theorem grow (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (w : ℕ → Pt κ) (q r : ℕ) (B : Pt κ) (hqr : q + r ≤ L n)
    (hstar : EHG.stab hreg hθ c (L n - q) q w = star)
    (hwB : ∀ i, i < q → w i ≤ B)
    (hmono : StrictMonoOn w (Set.Iio q)) :
    ∃ (w' : ℕ → Pt κ) (B' : Pt κ),
      B ≤ B' ∧
      (∀ i, i < q → w' i = w i) ∧
      (∀ i, i < q + r → w' i ≤ B') ∧
      (∀ i, q ≤ i → i < q + r → B < w' i) ∧
      StrictMonoOn w' (Set.Iio (q + r)) ∧
      EHG.stab hreg hθ c (L n - (q + r)) (q + r) w' = star := by
  induction' r with r ih;
  · exact ⟨ w, B, le_rfl, fun i hi => rfl, fun i hi => hwB i hi, fun i hi₁ hi₂ => by linarith, hmono, hstar ⟩;
  · obtain ⟨ w', B', hB', hw', hB'', hB''', hB'''' ⟩ := ih ( by linarith );
    obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( q + r ) - 1 ) ( q + r ) w' B';
    refine' ⟨ Function.update w' ( q + r ) z, z, _, _, _, _, _ ⟩;
    · exact le_trans hB' hz₁.le;
    · grind;
    · intro i hi; by_cases hi' : i = q + r <;> simp_all +decide [ Function.update_apply ] ;
      exact le_trans ( hB'' i ( by omega ) ) ( le_of_lt hz₁ );
    · grind +revert;
    · refine' ⟨ _, _ ⟩;
      · intro i hi j hj hij; simp_all +decide [ Function.update_apply ] ;
        split_ifs <;> try linarith;
        · exact lt_of_le_of_lt ( hB'' i ( by omega ) ) hz₁;
        · exact hB'''' |>.1 ( show i < q + r from by omega ) ( show j < q + r from by omega ) hij;
      · grind +qlia

/-
**Alternating middle run.**  Place the `s` interleaved pairs
`(wu (n+t), wv t)` for `t = t0, …, t0+s-1`, each above the running bound, so that
`wu (n+t) < wv t < wu (n+t+1)`.  Proved by induction on `s`.
-/
theorem mid (hreg : κ.IsRegular) (hθ : θ < κ) (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (wu wv : ℕ → Pt κ) (t0 s : ℕ) (B : Pt κ)
    (hs : n + t0 + s ≤ L n)
    (hstaru : EHG.stab hreg hθ c (L n - (n + t0)) (n + t0) wu = star)
    (hstarv : EHG.stab hreg hθ c (L n - t0) t0 wv = star)
    (hwuB : ∀ i, i < n + t0 → wu i ≤ B)
    (hwvB : ∀ i, i < t0 → wv i ≤ B)
    (hmonou : StrictMonoOn wu (Set.Iio (n + t0)))
    (hmonov : StrictMonoOn wv (Set.Iio t0)) :
    ∃ (wu' wv' : ℕ → Pt κ) (B' : Pt κ),
      B ≤ B' ∧
      (∀ i, i < n + t0 → wu' i = wu i) ∧
      (∀ i, i < t0 → wv' i = wv i) ∧
      (∀ i, i < n + t0 + s → wu' i ≤ B') ∧
      (∀ i, i < t0 + s → wv' i ≤ B') ∧
      StrictMonoOn wu' (Set.Iio (n + t0 + s)) ∧
      StrictMonoOn wv' (Set.Iio (t0 + s)) ∧
      EHG.stab hreg hθ c (L n - (n + t0 + s)) (n + t0 + s) wu' = star ∧
      EHG.stab hreg hθ c (L n - (t0 + s)) (t0 + s) wv' = star ∧
      (∀ t, t0 ≤ t → t < t0 + s → wu' (n + t) < wv' t) ∧
      (∀ t, t0 ≤ t → t + 1 < t0 + s → wv' t < wu' (n + t + 1)) := by
  induction' s with s ih generalizing t0 wu wv B;
  · exact ⟨ wu, wv, B, le_rfl, fun i hi => rfl, fun i hi => rfl, hwuB, hwvB, hmonou, hmonov, hstaru, hstarv, by intros; linarith, by intros; linarith ⟩;
  · obtain ⟨ wu', wv', B', hB', hwu', hwv', hwuB', hwvB', hmonou', hmonov', hstaru', hstarv', hlow', hhigh' ⟩ := ih wu wv t0 B ( by linarith ) hstaru hstarv hwuB hwvB hmonou hmonov;
    obtain ⟨ zu, hzu₁, hzu₂, hzu₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( n + t0 + s ) - 1 ) ( n + t0 + s ) wu' B';
    obtain ⟨ zv, hzv₁, hzv₂, hzv₃ ⟩ := EHG.exists_next_star hreg hθ c ( L n - ( t0 + s ) - 1 ) ( t0 + s ) wv' zu;
    refine' ⟨ Function.update wu' ( n + t0 + s ) zu, Function.update wv' ( t0 + s ) zv, zv, _, _, _, _, _ ⟩;
    · exact le_trans hB' ( le_trans hzu₁.le hzv₁.le );
    · grind +qlia;
    · grind;
    · grind +splitImp;
    · refine' ⟨ _, _, _, _, _ ⟩;
      · grind;
      · intro i hi j hj hij;
        by_cases hi' : i = n + t0 + s <;> by_cases hj' : j = n + t0 + s <;> simp +decide [ *, Function.update_apply ] at hij ⊢;
        · linarith [ Set.mem_Iio.mp hi, Set.mem_Iio.mp hj ];
        · exact lt_of_le_of_lt ( hwuB' i hij ) hzu₁;
        · exact hmonou' ( show i < n + t0 + s from lt_of_le_of_ne ( Nat.le_of_lt_succ hi ) hi' ) ( show j < n + t0 + s from lt_of_le_of_ne ( Nat.le_of_lt_succ hj ) hj' ) hij;
      · intro i hi j hj hij; simp_all +decide [ Function.update_apply ] ;
        split_ifs <;> try linarith;
        · exact lt_of_le_of_lt ( hwvB' i ( by omega ) ) ( lt_of_lt_of_le hzu₁ ( le_of_lt hzv₁ ) );
        · exact hmonov' ( show i < t0 + s from by omega ) ( show j < t0 + s from by omega ) hij;
      · grind;
      · grind

/-- **The extraction.**  From a fully stabilized tower (`stab … (L n) 0` constantly
`star`), read off two strictly increasing `L`-tuples `wu`, `wv` of common colour
`star` that interleave as a `GS_n` edge:
```
  wu_n < wv_0 < wu_{n+1} < wv_1 < ⋯ < wu_{n²+n} < wv_{n²}
```
(with `wu_0..wu_{n-1}` below and `wv_{n²+1}..wv_{n²+n}` above).  This is the only
`GS_n`-specific ingredient of the chromatic bound; it is built greedily with
`EHG.exists_next_star`, placing the `2·(L n)` coordinates in increasing order —
`wu_0,…,wu_{n-1}`, then alternately `wu_{n+t}, wv_t` for `t = 0,…,n²`, then
`wv_{n²+1},…,wv_{n²+n}` — each above a running bound so the merged chain is
strictly increasing (giving the interleaving) and each placement preserves its
tuple's stabilized colour (giving `c wu = c wv = star`). -/
theorem extract_gsn (hreg : κ.IsRegular) (hθ : θ < κ)
    (c : (ℕ → Pt κ) → θ.out) (star : θ.out)
    (hstar : ∀ w, EHG.stab hreg hθ c (L n) 0 w = star) :
    ∃ (wu wv : ℕ → Pt κ),
      StrictMono (fun i : Fin (L n) => wu i) ∧
      StrictMono (fun i : Fin (L n) => wv i) ∧
      c wu = star ∧ c wv = star ∧
      IsEdge (fun i : Fin (L n) => wu i) (fun i : Fin (L n) => wv i) := by
  classical
  haveI hInf : Infinite (Pt κ) := Cardinal.infinite_iff.2 (by simpa using! hreg.1)
  obtain ⟨p0⟩ : Nonempty (Pt κ) := inferInstance
  -- Phase 1: place wu₀ … wu_{n-1}.
  obtain ⟨wu1, B1, -, -, hwu1le, -, hwu1mono, hwu1stab⟩ :=
    grow (n := n) hreg hθ c star (fun _ => p0) 0 n p0
      (by simp only [L]; omega) (by simpa using! hstar (fun _ => p0))
      (by intro i hi; omega) (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)
  simp only [Nat.zero_add] at hwu1le hwu1mono hwu1stab
  -- Phase 2: alternately place wu_{n+t}, wv_t for t = 0 … n².
  obtain ⟨wu2, wv2, B2, -, -, -, hwu2le, hwv2le, hwu2mono, hwv2mono,
      hwu2stab, hwv2stab, hlow, hhigh⟩ :=
    mid (n := n) hreg hθ c star wu1 (fun _ => p0) 0 (n * n + 1) B1
      (by simp only [L]; omega) (by simpa using! hwu1stab)
      (by simpa using! hstar (fun _ => p0)) (by simpa using! hwu1le)
      (by intro i hi; omega) (by simpa using! hwu1mono)
      (by intro a ha b hb hab; simp only [Set.mem_Iio] at ha; omega)
  -- Phase 3: place wv_{n²+1} … wv_{n²+n}.
  obtain ⟨wv3, B3, -, hwv3agree, -, -, hwv3mono, hwv3stab⟩ :=
    grow (n := n) hreg hθ c star wv2 (n * n + 1) n B2
      (by simp only [L]; omega) (by simpa using! hwv2stab)
      (by simpa using! hwv2le) (by simpa using! hwv2mono)
  -- index normalizations
  have hidxu : n + 0 + (n * n + 1) = L n := by simp only [L]; ring
  have hidxv : n * n + 1 + n = L n := by simp only [L]; ring
  refine ⟨wu2, wv3, ?_, ?_, ?_, ?_, ?_⟩
  · -- StrictMono wu2
    have hm := hwu2mono; rw [hidxu] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  · -- StrictMono wv3
    have hm := hwv3mono; rw [hidxv] at hm
    intro a b hab
    exact hm (Set.mem_Iio.mpr a.2) (Set.mem_Iio.mpr b.2) hab
  · -- c wu2 = star
    have h := hwu2stab; rw [hidxu, Nat.sub_self] at h
    exact h
  · -- c wv3 = star
    have h := hwv3stab; rw [hidxv, Nat.sub_self] at h
    exact h
  · -- IsEdge
    refine ⟨?_, ?_⟩
    · intro t ht
      show wu2 (n + t) < wv3 t
      rw [hwv3agree t (by omega)]
      exact hlow t (Nat.zero_le _) (by omega)
    · intro t ht
      show wv3 t < wu2 (n + t + 1)
      rw [hwv3agree t (by omega)]
      exact hhigh t (Nat.zero_le _) (by omega)

/-- **Chromatic lower bound at a regular cardinal.**  For `κ` regular and
`θ < κ`, `graph n κ` is not `θ`-colourable.  (Erdős–Rado peeling; the extraction
reads two interleaving `L`-tuples of a common stabilized colour.) -/
theorem not_colorableBy_regular (hreg : κ.IsRegular) (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph n κ)).ColorableBy θ := by
  by_contra h_contra
  obtain ⟨c0, hc0'⟩ := h_contra
  have hproper : ∀ a b : Vtx n κ, (graph n κ).Adj a b → c0 a ≠ c0 b :=
    fun a b hab => (toHG_proper_iff _ c0).1 hc0' a b hab
  obtain ⟨x0, -⟩ : ∃ _ : Vtx n κ, True := by
    have h_inf : Infinite (Pt κ) := Cardinal.infinite_iff.2 (by simpa using! hreg.1)
    obtain ⟨s, hs⟩ : ∃ s : Finset (Pt κ), s.card = L n := by
      have hemb := h_inf.natEmbedding
      exact ⟨Finset.image (fun i : Fin (L n) => hemb i) Finset.univ, by
        rw [Finset.card_image_of_injective _ fun i j hij => by
          simpa [Fin.ext_iff] using! hemb.injective hij]; simp⟩
    exact ⟨⟨fun i => s.orderEmbOfFin (by aesop) i, by aesop_cat⟩, trivial⟩
  set junk := c0 x0 with hjunk
  set c := EHG.toTotal (L n) c0 junk with hc_def
  have hc : ∀ w w' : ℕ → Pt κ, (∀ i < L n, w i = w' i) → c w = c w' :=
    EHG.toTotal_prefix (L n) c0 junk
  obtain ⟨star, hstar⟩ : ∃ star : θ.out, ∀ w : ℕ → Pt κ,
      EHG.stab hreg hθ c (L n) 0 w = star := by
    refine ⟨EHG.stab hreg hθ c (L n) 0 (fun _ => x0.1 ⟨0, L_pos n⟩), fun w => ?_⟩
    exact EHG.stab_congr hreg hθ c hc (L n) 0 (by omega) w _ (fun i hi => by omega)
  obtain ⟨wu, wv, hwu_mono, hwv_mono, hcu, hcv, hedge⟩ := extract_gsn hreg hθ c star hstar
  set au : Vtx n κ := ⟨fun i => wu i, hwu_mono⟩ with hau
  set av : Vtx n κ := ⟨fun i => wv i, hwv_mono⟩ with hav
  have e1 : c wu = c0 au := EHG.toTotal_mono (L n) c0 junk wu hwu_mono
  have e2 : c wv = c0 av := EHG.toTotal_mono (L n) c0 junk wv hwv_mono
  have hne : c0 au ≠ c0 av := hproper au av (Or.inl hedge)
  apply hne
  rw [← e1, ← e2, hcu, hcv]

/-- **The chromatic lower bound (no regularity assumption).**  For `ℵ₀ < κ`,
`graph n κ` is not `θ`-colourable for any `θ < κ`. -/
theorem not_colorableBy (hκ : ℵ₀ < κ) (hθ : θ < κ) :
    ¬ (SimpleGraph.toHG (graph n κ)).ColorableBy θ := by
  intro h
  have hνκ : max θ ℵ₀ < κ := max_lt hθ hκ
  have hμκ : Order.succ (max θ ℵ₀) ≤ κ := Order.succ_le_of_lt hνκ
  have hμreg : (Order.succ (max θ ℵ₀)).IsRegular := Cardinal.isRegular_succ (le_max_right _ _)
  have hθμ : θ < Order.succ (max θ ℵ₀) := lt_of_le_of_lt (le_max_left _ _) (Order.lt_succ _)
  exact not_colorableBy_regular hμreg hθμ (colorableBy_of_le hμκ h)

end GSn
end Erdos1177
