import ErdosProblems.Erdos59.U2Direct
import ErdosProblems.Erdos59.U4Final
import ErdosProblems.Erdos59.U8Shortcut

/-!
# A coarse unconditional upper bound for the hexagon extremal number

The sharp Füredi--Naor--Verstraëte upper constant is not needed for the
Morris--Saxton counterexample when the four-fold matching blow-up is used.
This file proves the simpler eventual estimate

`ex(n, C₆) < (16 / 25) n^(4/3)`.

The proof uses only the large-girth degree comparison (U2--U3), the general
three-edge-path lower bound (U4), and the exceptional-multiplicity estimate
(U8).  A least counterexample to a bound with leading constant `63 / 100`
has minimum degree large enough for U3 to give `Δ ≤ 200 n^(1/3)`.
U4 and U8 then give an impossible scalar inequality.  Finally the strict
gap `63/100 < 16/25` absorbs the fixed linear error.
-/

open scoped BigOperators
open Finset SimpleGraph

namespace Erdos59

noncomputable section

private def weakLeading : ℝ := 63 / 100

private def weakLinear : ℝ := 10000

private def weakThreshold (n : ℕ) : ℝ :=
  weakLeading * (n : ℝ) ^ (4 / 3 : ℝ) + weakLinear * n

private theorem weakLeading_pos : 0 < weakLeading := by
  norm_num [weakLeading]

private theorem weakThreshold_nonneg (n : ℕ) : 0 ≤ weakThreshold n := by
  unfold weakThreshold weakLeading weakLinear
  positivity

/-! ## Elementary real-power calculus -/

/-- An elementary lower secant estimate used when one vertex is deleted. -/
private theorem rpow_four_thirds_step_lower {x : ℝ} (hx : 1 ≤ x) :
    x ^ (1 / 3 : ℝ) - 1 ≤
      x ^ (4 / 3 : ℝ) - (x - 1) ^ (4 / 3 : ℝ) := by
  by_cases hxeq : x = 1
  · subst x
    norm_num
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hxsubpos : 0 < x - 1 := sub_pos.mpr (lt_of_le_of_ne hx (Ne.symm hxeq))
  have hroot : x ^ (1 / 3 : ℝ) ≤ (x - 1) ^ (1 / 3 : ℝ) + 1 := by
    have h := Real.rpow_add_le_add_rpow (sub_nonneg.mpr hx) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (1 / 3 : ℝ) ≤ 1)
    simpa using h
  have hmono : (x - 1) ^ (1 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) := by
    exact Real.rpow_le_rpow (sub_nonneg.mpr hx) (by linarith) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hmono hxpos.le
  have hxpow : x ^ (4 / 3 : ℝ) = x * x ^ (1 / 3 : ℝ) := by
    calc
      x ^ (4 / 3 : ℝ) = x ^ ((1 : ℝ) + 1 / 3) := by norm_num
      _ = x ^ (1 : ℝ) * x ^ (1 / 3 : ℝ) := Real.rpow_add hxpos 1 (1 / 3)
      _ = _ := by rw [Real.rpow_one]
  have hxsubpow :
      (x - 1) ^ (4 / 3 : ℝ) = (x - 1) * (x - 1) ^ (1 / 3 : ℝ) := by
    calc
      (x - 1) ^ (4 / 3 : ℝ) = (x - 1) ^ ((1 : ℝ) + 1 / 3) := by norm_num
      _ = (x - 1) ^ (1 : ℝ) * (x - 1) ^ (1 / 3 : ℝ) :=
        Real.rpow_add hxsubpos 1 (1 / 3)
      _ = _ := by rw [Real.rpow_one]
  rw [hxpow, hxsubpow]
  nlinarith

private theorem weakThreshold_step_lower {n : ℕ} (hn : 0 < n) :
    (63 / 100 : ℝ) * ((n : ℝ) ^ (1 / 3 : ℝ) - 1) + weakLinear ≤
      weakThreshold n - weakThreshold (n - 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hdiff := rpow_four_thirds_step_lower hn1
  have hmul := mul_le_mul_of_nonneg_left hdiff weakLeading_pos.le
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
    norm_num
  unfold weakThreshold weakLeading weakLinear
  rw [hcast]
  norm_num at hmul ⊢
  nlinarith

private theorem nat_rpow_one_third_cube {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
  norm_num

private theorem nat_rpow_four_thirds_eq {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ (4 / 3 : ℝ) =
      (n : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnℝ : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    (n : ℝ) ^ (4 / 3 : ℝ) =
        (n : ℝ) ^ ((1 : ℝ) + 1 / 3) := by norm_num
    _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.rpow_add hnℝ 1 (1 / 3)
    _ = _ := by rw [Real.rpow_one]

/-! ## Direct U3 and the standard cycle predicate -/

private theorem walkC6Free_of_free {V : Type*} (G : SimpleGraph V)
    (hfree : (SimpleGraph.cycleGraph 6).Free G) : WalkC6Free G := by
  intro v q hq hlen
  apply hfree
  rw [SimpleGraph.cycleGraph_isContained_iff (by omega : 2 < 6)]
  exact ⟨v, q, hq, hlen⟩

/-- U2 supplies the certificate required by the graph-level U3 theorem. -/
private theorem degree_comparison_direct
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : (SimpleGraph.cycleGraph 6).Free G) :
    G.maxDegree * (G.minDegree - 4) ^ 2 ≤ 64 * Fintype.card V := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h => simp
  | inr h =>
      apply GirthDegree.degree_comparison G G.minDegree G.maxDegree
      · exact fun v ↦ G.minDegree_le_degree v
      · obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
        exact ⟨v, hv.symm⟩
      · exact hfree
      · intro c _hc
        exact GirthDegree.Bigraph.quadrilateralForestCertificate_direct
          (GirthDegree.crossingBigraph G c)
          (GirthDegree.crossingBigraph_noSixCycle_of_free G hfree c)

/-! ## Identifying the U4 and U8 path counts -/

private abbrev U4PathIndex {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  Σ u : V, Σ v : {v // v ∈ G.neighborFinset u},
    {p : V × V // p ∈ u4LocalPaths G u v}

private def u4IndexPath {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : U4PathIndex G) :
    Fin 4 → V :=
  ![z.2.2.1.1, z.1, z.2.1.1, z.2.2.1.2]

private theorem u4IndexPath_isPath3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : U4PathIndex G) :
    IsPath3 G (u4IndexPath G z) := by
  rcases Finset.mem_filter.mp z.2.2.2 with ⟨hp, hne⟩
  rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
  have huv : G.Adj z.1 z.2.1.1 := (G.mem_neighborFinset _ _).1 z.2.1.2
  have hux : G.Adj z.1 z.2.2.1.1 := (G.mem_neighborFinset _ _).1 hx
  have hvy : G.Adj z.2.1.1 z.2.2.1.2 := (G.mem_neighborFinset _ _).1 hy
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [u4IndexPath, G.loopless]
  · exact ⟨hux.symm, huv, hvy⟩

private def path3ToU4Index {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Path3 G ⊕ Path3 G → U4PathIndex G
  | Sum.inl p =>
      ⟨p.vertex 1, ⟨⟨p.vertex 2, by
          apply (G.mem_neighborFinset _ _).2
          exact p.adj_one_two⟩,
        ⟨(p.vertex 0, p.vertex 3), by
          rw [u4LocalPaths, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨(G.mem_neighborFinset _ _).2 p.adj_zero_one.symm,
            (G.mem_neighborFinset _ _).2 p.adj_two_three⟩,
            p.injective.ne (by decide), p.injective.ne (by decide),
            p.injective.ne (by decide)⟩⟩⟩⟩
  | Sum.inr p =>
      ⟨p.vertex 2, ⟨⟨p.vertex 1, by
          apply (G.mem_neighborFinset _ _).2
          exact p.adj_one_two.symm⟩,
        ⟨(p.vertex 3, p.vertex 0), by
          rw [u4LocalPaths, Finset.mem_filter, Finset.mem_product]
          exact ⟨⟨(G.mem_neighborFinset _ _).2 p.adj_two_three,
            (G.mem_neighborFinset _ _).2 p.adj_zero_one.symm⟩,
            p.injective.ne (by decide), p.injective.ne (by decide),
            p.injective.ne (by decide)⟩⟩⟩⟩

private def u4IndexToPath3 {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    U4PathIndex G → Path3 G ⊕ Path3 G := fun z ↦
  if h : z.2.2.1.1 < z.2.2.1.2 then
    Sum.inl ⟨u4IndexPath G z, u4IndexPath_isPath3 G z, h⟩
  else
    Sum.inr ⟨u4IndexPath G z ∘ Fin.rev, by
      have hp := u4IndexPath_isPath3 G z
      constructor
      · exact hp.1.comp Fin.rev_injective
      · exact ⟨by simpa [Function.comp_def] using hp.2.2.2.symm,
          by simpa [Function.comp_def] using hp.2.2.1.symm,
          by simpa [Function.comp_def] using hp.2.1.symm⟩,
      by
        have hne := (u4IndexPath_isPath3 G z).1.ne
          (show (0 : Fin 4) ≠ 3 by decide)
        simpa [Function.comp_def, u4IndexPath] using
          (lt_of_le_of_ne (le_of_not_gt h) hne.symm)⟩

private def u4PathIndexEquivPath3Sum {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    U4PathIndex G ≃ Path3 G ⊕ Path3 G where
  toFun := u4IndexToPath3 G
  invFun := path3ToU4Index G
  left_inv := by
    intro z
    rw [u4IndexToPath3]
    split_ifs with h
    · rfl
    · rfl
  right_inv := by
    intro p
    cases p with
    | inl p =>
        rw [path3ToU4Index, u4IndexToPath3]
        split_ifs with h
        · apply congrArg Sum.inl
          apply Subtype.ext
          funext i
          fin_cases i <;> rfl
        · exact (h p.2.2).elim
    | inr p =>
        rw [path3ToU4Index, u4IndexToPath3]
        split_ifs with h
        · exact (lt_asymm h p.2.2).elim
        · apply congrArg Sum.inr
          apply Subtype.ext
          funext i
          fin_cases i <;> rfl

private theorem card_u4PathIndex {V : Type*} [Fintype V] [DecidableEq V]
    [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (U4PathIndex G) = u4OrientedPathCount G := by
  simp only [U4PathIndex, Fintype.card_sigma, Fintype.card_coe]
  unfold u4OrientedPathCount
  apply Finset.sum_congr rfl
  intro u _hu
  exact Finset.sum_attach (G.neighborFinset u)
    (fun v ↦ (u4LocalPaths G u v).card)

private theorem u4PathCount_eq_card_path3 {V : Type*} [Fintype V]
    [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    u4PathCount G = Fintype.card (Path3 G) := by
  have hcard := Fintype.card_congr (u4PathIndexEquivPath3Sum G)
  rw [card_u4PathIndex G] at hcard
  simp only [Fintype.card_sum] at hcard
  unfold u4PathCount
  rw [hcard]
  norm_num

private theorem card_endpointPair_twice_le {V : Type*} [Fintype V] [LinearOrder V] :
    2 * Fintype.card (EndpointPair V) ≤ Fintype.card V ^ 2 := by
  let f : EndpointPair V ⊕ EndpointPair V → V × V
    | Sum.inl z => z.1
    | Sum.inr z => (z.1.2, z.1.1)
  have hf : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            congr 1
            exact Subtype.ext hxy
        | inr y =>
            exfalso
            have h1 : x.1.1 = y.1.2 := congrArg Prod.fst hxy
            have h2 : x.1.2 = y.1.1 := congrArg Prod.snd hxy
            exact (lt_asymm x.2 (by simpa [h1, h2] using y.2))
    | inr x =>
        cases y with
        | inl y =>
            exfalso
            have h1 : x.1.2 = y.1.1 := congrArg Prod.fst hxy
            have h2 : x.1.1 = y.1.2 := congrArg Prod.snd hxy
            exact (lt_asymm x.2 (by simpa [h1, h2] using y.2))
        | inr y =>
            congr 1
            apply Subtype.ext
            exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_sum, Fintype.card_prod, two_mul, pow_two] using hcard

private noncomputable def path3SigmaEquiv
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Path3 G ≃ Σ pi : EndpointPair V, pathFiber G pi where
  toFun p := ⟨p.endpoints, ⟨p, by simp⟩⟩
  invFun z := z.2.1
  left_inv p := rfl
  right_inv z := by
    rcases z with ⟨pi, ⟨p, hp⟩⟩
    have hpi : p.endpoints = pi := (mem_pathFiber G).1 hp
    cases hpi
    rfl

private theorem card_path3_eq_sum_multiplicity
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Path3 G) = ∑ pi, pathMultiplicity G pi := by
  calc
    Fintype.card (Path3 G) =
        Fintype.card (Σ pi : EndpointPair V, pathFiber G pi) :=
      Fintype.card_congr (path3SigmaEquiv G)
    _ = ∑ pi : EndpointPair V, (pathFiber G pi).card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]
    _ = ∑ pi, pathMultiplicity G pi := by
      rfl

private theorem card_path3_le_sq_add_exceptional
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fintype.card (Path3 G) ≤
      Fintype.card V ^ 2 +
        ∑ pi ∈ generalExceptionalPairs G, pathMultiplicity G pi := by
  classical
  let : DecidableEq V := Classical.typeDecidableEq V
  let E := generalExceptionalPairs G
  have hsmall : ∀ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
      pathMultiplicity G pi ≤ 2 := by
    intro pi hpi
    have hn : pi ∉ ordinaryExceptionalPairs G := by
      intro h
      exact (Finset.mem_sdiff.mp hpi).2 (Finset.mem_union_left _ h)
    simp only [ordinaryExceptionalPairs, Finset.mem_filter, Finset.mem_univ,
      true_and, not_or] at hn
    omega
  have hrest :
      ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
          pathMultiplicity G pi ≤ Fintype.card V ^ 2 := by
    calc
      ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
          pathMultiplicity G pi ≤
          ∑ _pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E, 2 := by
            exact Finset.sum_le_sum hsmall
      _ = 2 * ((Finset.univ : Finset (EndpointPair V)) \ E).card := by
        have hsum := Finset.sum_const_nat
          (s := (Finset.univ : Finset (EndpointPair V)) \ E)
          (m := 2) (f := fun _pi : EndpointPair V ↦ 2) (by simp)
        simpa [Nat.mul_comm] using hsum
      _ ≤ 2 * Fintype.card (EndpointPair V) := by
        exact Nat.mul_le_mul_left 2 (Finset.card_le_univ _)
      _ ≤ Fintype.card V ^ 2 := card_endpointPair_twice_le
  rw [card_path3_eq_sum_multiplicity G]
  have hsplit :
      ∑ pi : EndpointPair V, pathMultiplicity G pi =
        (∑ pi ∈ E, pathMultiplicity G pi) +
          ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
            pathMultiplicity G pi := by
    have h := Finset.sum_sdiff (f := pathMultiplicity G)
      (Finset.subset_univ E)
    simpa [add_comm] using h.symm
  rw [hsplit]
  calc
    (∑ pi ∈ E, pathMultiplicity G pi) +
          ∑ pi ∈ (Finset.univ : Finset (EndpointPair V)) \ E,
            pathMultiplicity G pi ≤
        (∑ pi ∈ E, pathMultiplicity G pi) + Fintype.card V ^ 2 :=
      Nat.add_le_add_left hrest _
    _ = Fintype.card V ^ 2 +
        ∑ pi ∈ E, pathMultiplicity G pi := Nat.add_comm _ _

private theorem u4PathCount_le_sq_add_thirtyfive
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hC6 : WalkC6Free G) :
    u4PathCount G ≤ (Fintype.card V : ℝ) ^ 2 +
      35 * (G.maxDegree : ℝ) * G.edgeFinset.card := by
  have hcard := card_path3_le_sq_add_exceptional G
  have hexceptional := fnvU8Direct G hC6
  unfold multiplicitySum at hexceptional
  rw [u4PathCount_eq_card_path3 G]
  have hnat := hcard.trans (Nat.add_le_add_left hexceptional _)
  exact_mod_cast hnat

/-! ## Least-counterexample setup -/

private theorem exists_minimal_weak_counterexample
    (hfail : ¬ ∀ n : ℕ,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ≤
        weakThreshold n) :
    ∃ n : ℕ,
      weakThreshold n <
          (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ∧
        ∀ m < n,
          (SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) : ℝ) ≤
            weakThreshold m := by
  push_neg at hfail
  let n := Nat.find hfail
  refine ⟨n, Nat.find_spec hfail, ?_⟩
  intro m hm
  exact le_of_not_gt fun hbad ↦ Nat.find_min hfail hm hbad

/-! ## Scalar contradiction -/

/-- The numerical inequality at the end of the coarse U3--U4--U8 argument.
Writing `t=n^(1/3)`, U4--U8 gives the first displayed hypothesis; U3 gives
the second.  The assumed edge lower bound makes them inconsistent. -/
private theorem no_weak_scalar_counterexample
    {n e Delta t : ℝ}
    (hn : 0 < n) (ht : 0 < t) (ht3 : t ^ 3 = n)
    (he : n * ((63 / 100 : ℝ) * t + 10000) < e)
    (hDelta : Delta ≤ 200 * t)
    (hpaths : 4 * e ^ 3 / n ^ 2 ≤ n ^ 2 + 38 * Delta * e) : False := by
  have hfactor : 0 < (63 / 100 : ℝ) * t + 10000 := by positivity
  have he0 : 0 < e := (mul_pos hn hfactor).trans he
  have hratio : (63 / 100 : ℝ) * t + 10000 < e / n := by
    exact (lt_div_iff₀ hn).2 (by nlinarith)
  have hmain : 4 * (e / n) ^ 2 ≤ n ^ 2 / e + 38 * Delta := by
    calc
      4 * (e / n) ^ 2 = (4 * e ^ 3 / n ^ 2) / e := by field_simp
      _ ≤ (n ^ 2 + 38 * Delta * e) / e :=
        div_le_div_of_nonneg_right hpaths he0.le
      _ = n ^ 2 / e + 38 * Delta := by field_simp
  have hleft :
      4 * ((63 / 100 : ℝ) * t + 10000) ^ 2 < 4 * (e / n) ^ 2 := by
    have hbase : 0 ≤ (63 / 100 : ℝ) * t + 10000 := by positivity
    nlinarith [sq_nonneg (e / n - ((63 / 100 : ℝ) * t + 10000))]
  have hcoarse : (63 / 100 : ℝ) * t * n < e := by
    nlinarith
  have hright : n ^ 2 / e < (100 / 63 : ℝ) * t ^ 2 := by
    apply (div_lt_iff₀ he0).2
    have hmul := mul_lt_mul_of_pos_left hcoarse (show 0 < (100 / 63 : ℝ) * t ^ 2 by positivity)
    rw [← ht3] at hmul ⊢
    nlinarith
  have hDelta' : 38 * Delta ≤ 7600 * t := by nlinarith
  have hfinal :
      4 * ((63 / 100 : ℝ) * t + 10000) ^ 2 <
        (100 / 63 : ℝ) * t ^ 2 + 7600 * t := by
    linarith
  nlinarith [sq_nonneg t]

/-! ## The all-orders estimate with a linear error -/

private theorem extremalNumber_cycleGraph_six_le_weakThreshold (n : ℕ) :
    (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) ≤
      weakThreshold n := by
  by_contra hthis
  have hglobal : ¬ ∀ m : ℕ,
      (SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) : ℝ) ≤
        weakThreshold m := by
    intro h
    exact hthis (h n)
  obtain ⟨m, hmfail, hmmin⟩ := exists_minimal_weak_counterexample hglobal
  have hm : 0 < m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    have hex0 : SimpleGraph.extremalNumber 0 (SimpleGraph.cycleGraph 6) = 0 := by
      have hle : SimpleGraph.extremalNumber 0 (SimpleGraph.cycleGraph 6) ≤ 0 := by
        rw [← Fintype.card_fin 0, SimpleGraph.extremalNumber_le_iff]
        intro G _inst _hfree
        have hbot : G = ⊥ := Subsingleton.elim _ _
        simp [hbot]
      omega
    simp [weakThreshold, hex0] at hmfail
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let t : ℝ := (m : ℝ) ^ (1 / 3 : ℝ)
  have hmℝ : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht : 0 < t := by positivity
  have ht3 : t ^ 3 = (m : ℝ) := by
    simpa [t] using nat_rpow_one_third_cube hm
  have hpow : (m : ℝ) ^ (4 / 3 : ℝ) = (m : ℝ) * t := by
    simpa [t] using nat_rpow_four_thirds_eq hm

  obtain ⟨G, inst, hGext⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      ((SimpleGraph.cycleGraph 6).Free : SimpleGraph (Fin m) → Prop)).2
      ⟨⊥, SimpleGraph.free_bot (by
        intro hbot
        have hadj : (SimpleGraph.cycleGraph 6).Adj 0 1 := by decide
        rw [hbot] at hadj
        exact hadj)⟩
  let : DecidableRel G.Adj := inst
  have hfree : (SimpleGraph.cycleGraph 6).Free G := hGext.prop
  have hedgeNat : G.edgeFinset.card =
      SimpleGraph.extremalNumber m (SimpleGraph.cycleGraph 6) := by
    simpa using SimpleGraph.card_edgeFinset_of_isExtremal_free hGext
  let e : ℝ := G.edgeFinset.card
  have he : weakThreshold m < e := by simpa [e, hedgeNat] using hmfail
  have heExpanded :
      (m : ℝ) * ((63 / 100 : ℝ) * t + 10000) < e := by
    rw [weakThreshold, weakLeading, weakLinear, hpow] at he
    nlinarith

  have hdegree : ∀ v : Fin m,
      weakThreshold m - weakThreshold (m - 1) < (G.degree v : ℝ) := by
    intro v
    have hdelNat := G.card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
    have hprev := hmmin (m - 1) (by omega)
    have hdel : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) ≤
        weakThreshold (m - 1) := by
      have hdel' : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) ≤
          (SimpleGraph.extremalNumber (m - 1)
            (SimpleGraph.cycleGraph 6) : ℝ) := by
        have hdelNat' : (G.deleteIncidenceSet v).edgeFinset.card ≤
            SimpleGraph.extremalNumber (m - 1) (SimpleGraph.cycleGraph 6) := by
          simpa using hdelNat
        exact_mod_cast hdelNat'
      exact hdel'.trans hprev
    have hdeg_le : G.degree v ≤ G.edgeFinset.card := by
      rw [← G.card_incidenceFinset_eq_degree]
      exact Finset.card_le_card (G.incidenceFinset_subset v)
    have hdelete : ((G.deleteIncidenceSet v).edgeFinset.card : ℝ) =
        e - G.degree v := by
      rw [G.card_edgeFinset_deleteIncidenceSet, Nat.cast_sub hdeg_le]
    rw [hdelete] at hdel
    linarith
  obtain ⟨vmin, hvmin⟩ := G.exists_minimal_degree_vertex
  have hstep := weakThreshold_step_lower hm
  have hmindtStrong :
      (63 / 100 : ℝ) * (t - 1) + 10000 < G.minDegree := by
    have hv := hdegree vmin
    rw [← hvmin] at hv
    norm_num [weakLinear] at hstep
    nlinarith
  have hmindt : (63 / 100 : ℝ) * t < G.minDegree := by
    nlinarith
  have hmin4 : 4 ≤ G.minDegree := by
    have ht0 : 0 ≤ t := ht.le
    exact_mod_cast (show (4 : ℝ) ≤ G.minDegree by nlinarith)

  have hcompNat := degree_comparison_direct G hfree
  have hcomp : (G.maxDegree : ℝ) * ((G.minDegree - 4 : ℕ) : ℝ) ^ 2 ≤
      64 * (m : ℝ) := by
    have hcompNat' : G.maxDegree * (G.minDegree - 4) ^ 2 ≤ 64 * m := by
      simpa using hcompNat
    exact_mod_cast hcompNat'
  have hsub : ((G.minDegree - 4 : ℕ) : ℝ) = (G.minDegree : ℝ) - 4 := by
    rw [Nat.cast_sub hmin4]
    norm_num
  have hdt : (63 / 100 : ℝ) * t < ((G.minDegree - 4 : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith [hmindtStrong]
  have hsq : ((63 / 100 : ℝ) * t) ^ 2 ≤
      (((G.minDegree - 4 : ℕ) : ℝ)) ^ 2 := by
    have hleft : 0 ≤ (63 / 100 : ℝ) * t := by positivity
    nlinarith [sq_nonneg
      (((G.minDegree - 4 : ℕ) : ℝ) - (63 / 100 : ℝ) * t)]
  have hcomp' : (G.maxDegree : ℝ) * ((63 / 100 : ℝ) * t) ^ 2 ≤
      64 * (m : ℝ) := by
    calc
      (G.maxDegree : ℝ) * ((63 / 100 : ℝ) * t) ^ 2 ≤
          (G.maxDegree : ℝ) * (((G.minDegree - 4 : ℕ) : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      _ ≤ _ := hcomp
  have hDelta : (G.maxDegree : ℝ) ≤ 200 * t := by
    by_contra hnot
    have hgt : 200 * t < (G.maxDegree : ℝ) := lt_of_not_ge hnot
    have hpos : 0 < ((63 / 100 : ℝ) * t) ^ 2 := by positivity
    have hmul := mul_lt_mul_of_pos_right hgt hpos
    rw [← ht3] at hcomp'
    nlinarith [sq_pos_of_pos ht]

  have hwalk : WalkC6Free G := walkC6Free_of_free G hfree
  have hu4 := fnv_u4_general G
  have hu8 := u4PathCount_le_sq_add_thirtyfive G hwalk
  have hu4' : 4 * e ^ 3 / (m : ℝ) ^ 2 -
      3 * (G.maxDegree : ℝ) * e ≤ u4PathCount G := by
    simpa [e] using hu4
  have hu8' : u4PathCount G ≤
      (m : ℝ) ^ 2 + 35 * (G.maxDegree : ℝ) * e := by
    simpa [e] using hu8
  have hpaths : 4 * e ^ 3 / (m : ℝ) ^ 2 ≤
      (m : ℝ) ^ 2 + 38 * (G.maxDegree : ℝ) * e := by
    linarith
  exact no_weak_scalar_counterexample hmℝ ht ht3 heExpanded hDelta hpaths

/-! ## Absorbing the linear error at an explicit threshold -/

/-- A concrete finite version of the coarse upper bound.  The intentionally
large threshold keeps the final absorption calculation entirely rational. -/
theorem extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths_of_ge
    {n : ℕ} (hn : 1000001 ^ 3 ≤ n) :
    (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
      (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
  have hnpos : 0 < n := by omega
  have hbase : (0 : ℝ) ≤ (1000001 : ℝ) ^ 3 := by positivity
  have hcast : ((1000001 : ℝ) ^ 3) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrootMono :=
    Real.rpow_le_rpow hbase hcast (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hleft : (((1000001 : ℝ) ^ 3) ^ (1 / 3 : ℝ)) = 1000001 := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1000001)]
    norm_num
  rw [hleft] at hrootMono
  have hnroot : (1000000 : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) := by
    linarith
  have hpow := nat_rpow_four_thirds_eq hnpos
  have hthreshold : weakThreshold n <
      (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
    unfold weakThreshold weakLeading weakLinear
    rw [hpow]
    nlinarith
  exact (extremalNumber_cycleGraph_six_le_weakThreshold n).trans_lt hthreshold

/-- The unconditional coarse FNV upper bound used by the four-fold
Morris--Saxton construction. -/
theorem eventually_extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths :
    ∀ᶠ n : ℕ in Filter.atTop,
      (SimpleGraph.extremalNumber n (SimpleGraph.cycleGraph 6) : ℝ) <
        (16 / 25 : ℝ) * (n : ℝ) ^ (4 / 3 : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop (1000001 ^ 3)] with n hn
  exact extremalNumber_cycleGraph_six_lt_sixteen_twentyfifths_of_ge hn

end

end Erdos59
