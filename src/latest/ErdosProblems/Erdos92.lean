/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 92.
https://www.erdosproblems.com/forum/thread/92

Informal authors:
- L. Alpöge

Statement authors:
- Formal Conjectures authors

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos92.md
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/92.lean
-/
import ErdosProblems.Erdos90b

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open Filter
open scoped EuclideanGeometry

namespace Erdos92

def unitGraph (P : Finset ℝ²) : SimpleGraph P where
  Adj x y := dist (x : ℝ²) y = 1
  symm := ⟨by
    intro x y h
    simpa [dist_comm] using h⟩
  loopless := ⟨by
    intro x h
    simpa using h⟩

noncomputable instance (P : Finset ℝ²) : DecidableRel (unitGraph P).Adj := by
  classical
  unfold unitGraph
  infer_instance

lemma card_adj_pairs (P : Finset ℝ²) :
    ((Finset.univ : Finset (P × P)).filter fun xy => (unitGraph P).Adj xy.1 xy.2).card =
      (P.offDiag.filter fun xy => dist xy.1 xy.2 = 1).card := by
  classical
  apply Finset.card_bij (fun xy _ => ((xy.1 : ℝ²), (xy.2 : ℝ²)))
  · intro xy hxy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxy
    have hdist : dist (xy.1 : ℝ²) xy.2 = 1 := by
      simpa [unitGraph] using hxy
    simp only [Finset.mem_filter, Finset.mem_offDiag]
    exact ⟨⟨xy.1.property, xy.2.property, by
      intro h
      rw [h, dist_self] at hdist
      norm_num at hdist⟩, hdist⟩
  · intro a₁ h₁ a₂ h₂ h
    exact Prod.ext (Subtype.ext (Prod.ext_iff.mp h).1) (Subtype.ext (Prod.ext_iff.mp h).2)
  · intro xy hxy
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hxy
    refine ⟨(⟨xy.1, hxy.1.1⟩, ⟨xy.2, hxy.1.2.1⟩), ?_, rfl⟩
    have hne : (⟨xy.1, hxy.1.1⟩ : P) ≠ ⟨xy.2, hxy.1.2.1⟩ := by
      intro h
      exact hxy.1.2.2 (congrArg Subtype.val h)
    have hadj : (unitGraph P).Adj ⟨xy.1, hxy.1.1⟩ ⟨xy.2, hxy.1.2.1⟩ := by
      simpa [unitGraph] using hxy.2
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hadj

lemma card_edgeFinset_unitGraph (P : Finset ℝ²) :
    (unitGraph P).edgeFinset.card = Erdos.unitDist P := by
  classical
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
  rw [(unitGraph P).two_mul_card_edgeFinset, card_adj_pairs, Erdos.two_mul_unitDist]

def edgeCount {α : Type*} [Fintype α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (s : Finset α) : ℕ :=
  (G.induce (s : Set α)).edgeFinset.card

lemma edgeCount_univ {α : Type*} [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] :
    edgeCount G Finset.univ = G.edgeFinset.card := by
  classical
  let e : (↑(Finset.univ : Finset α) : Set α) ≃ α :=
    (Equiv.subtypeEquivRight (fun x : α => by simp)).trans (Equiv.Set.univ α)
  let iso : G.induce (↑(Finset.univ : Finset α) : Set α) ≃g G := {
    toEquiv := e
    map_rel_iff' := by
      intro x y
      rfl }
  simpa [edgeCount] using iso.card_edgeFinset_eq

open scoped Classical in
lemma edgeCount_erase {α : Type*} [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (s : Finset α) {v : α} (hv : v ∈ s) :
    edgeCount G (s.erase v) =
      edgeCount G s -
        ((s.erase v).filter fun w => G.Adj v w).card := by
  classical
  let H := G.induce (s : Set α)
  let vv : s := ⟨v, hv⟩
  let f : {x : α // x ∈ s.erase v} → {x : s // x ≠ vv} := fun x =>
    Subtype.mk (Subtype.mk x.1 (Finset.mem_of_mem_erase x.property)) (by
      intro h
      exact (Finset.mem_erase.mp x.property).1 (Subtype.ext_iff.mp h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (congrArg (fun z => (z.1 : α)) h)
    · intro x
      refine ⟨⟨x.1, ?_⟩, ?_⟩
      · rw [Finset.mem_erase]
        exact ⟨by
          intro h
          apply x.property
          exact Subtype.ext h, x.1.property⟩
      · exact Subtype.ext rfl
  let e : {x : α // x ∈ s.erase v} ≃ {x : s // x ≠ vv} :=
    Equiv.ofBijective f hf
  have iso : G.induce (s.erase v : Set α) ≃g H.induce ({vv}ᶜ : Set s) := {
    toEquiv := e
    map_rel_iff' := by
      intro x y
      change G.Adj (f x).1.1 (f y).1.1 ↔ G.Adj x.1 y.1
      rfl }
  have hcard :
      edgeCount G (s.erase v) = (H.induce ({vv}ᶜ : Set s)).edgeFinset.card := by
    simpa [edgeCount] using iso.card_edgeFinset_eq
  rw [hcard, SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  change H.edgeFinset.card - H.degree vv =
    edgeCount G s - ((s.erase v).filter fun w => G.Adj v w).card
  have hHs : H.edgeFinset.card = edgeCount G s := by
    rfl
  rw [hHs]
  congr 1
  rw [← H.card_neighborFinset_eq_degree, H.neighborFinset_eq_filter]
  refine Finset.card_bij (fun (w : s) _ => (w : α)) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    rw [Finset.mem_filter, Finset.mem_erase]
    refine ⟨⟨?_, w.property⟩, ?_⟩
    · intro h
      have hwv : w = vv := Subtype.ext h
      subst w
      exact H.loopless.irrefl vv hw
    · simpa [H, vv] using hw
  · intro a₁ h₁ a₂ h₂ h
    exact Subtype.ext h
  · intro w hw
    rw [Finset.mem_filter, Finset.mem_erase] at hw
    refine ⟨⟨w, hw.1.2⟩, ?_, rfl⟩
    simpa [H, vv] using hw.2

open scoped Classical in
lemma core_of_dense {α : Type*} [Fintype α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (k : ℕ) (s : Finset α)
    (h : k * s.card < edgeCount G s) :
    ∃ t : Finset α, t ⊆ s ∧ t.Nonempty ∧
      ∀ v ∈ t, k ≤ ((t.erase v).filter fun w => G.Adj v w).card := by
  classical
  refine Finset.strongInductionOn s ?_ h
  intro s ih h
  by_cases hall : ∀ v ∈ s, k ≤ ((s.erase v).filter fun w => G.Adj v w).card
  · refine ⟨s, Finset.Subset.rfl, ?_, hall⟩
    by_contra hs
    rw [Finset.not_nonempty_iff_eq_empty.mp hs] at h
    simp [edgeCount] at h
    apply h
    ext x y
    have hx : False := by simpa using x.property
    exact hx.elim
  · push_neg at hall
    obtain ⟨v, hv, hvdeg⟩ := hall
    have hs' : s.erase v ⊂ s := Finset.erase_ssubset hv
    have h' : k * (s.erase v).card < edgeCount G (s.erase v) := by
      rw [edgeCount_erase G s hv]
      have hcard : (s.erase v).card + 1 = s.card := Finset.card_erase_add_one hv
      rw [← hcard] at h
      simp only [Nat.mul_add, Nat.mul_one] at h
      omega
    obtain ⟨t, hts, htne, htdeg⟩ := ih (s.erase v) hs' h'
    exact ⟨t, hts.trans (Finset.erase_subset _ _), htne, htdeg⟩

noncomputable def maxEquidistantPointsAt (x : ℝ²) (points : Finset ℝ²) : ℕ :=
  letI otherPoints := points.erase x
  letI distances := otherPoints.image (dist x)
  sSup (distances.image fun d ↦ (otherPoints.filter fun p ↦ dist x p = d).card)

def hasMinEquidistantProperty (k : ℕ) (A : Finset ℝ²) : Prop :=
  A.Nonempty ∧ ∀ x ∈ A, k ≤ maxEquidistantPointsAt x A

noncomputable def possible_f_values (n : ℕ) : Set ℕ :=
  {k | ∃ (points : Finset ℝ²) (_ : points.card = n), hasMinEquidistantProperty k points}

theorem possible_f_values_BddAbove (n : ℕ) : BddAbove (possible_f_values n) := by
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨points, hcard, ⟨x, hx⟩, hall⟩ := hk
  refine (hall x hx).trans ?_
  unfold maxEquidistantPointsAt
  refine csSup_le' fun m hm => ?_
  rw [Finset.mem_coe, Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  calc ((points.erase x).filter fun p => dist x p = d).card
      ≤ (points.erase x).card := Finset.card_filter_le _ _
    _ ≤ points.card := Finset.card_erase_le
    _ = n := hcard

noncomputable def f (n : ℕ) : ℕ := sSup <| possible_f_values n

lemma possible_value_le_card {n k : ℕ} (hk : k ∈ possible_f_values n) : k ≤ n := by
  obtain ⟨points, hcard, ⟨x, hx⟩, hall⟩ := hk
  refine (hall x hx).trans ?_
  unfold maxEquidistantPointsAt
  refine csSup_le' fun m hm => ?_
  rw [Finset.mem_coe, Finset.mem_image] at hm
  obtain ⟨d, hd, rfl⟩ := hm
  calc ((points.erase x).filter fun p => dist x p = d).card
      ≤ (points.erase x).card := Finset.card_filter_le _ _
    _ ≤ points.card := Finset.card_erase_le
    _ = n := hcard

open scoped Classical in
lemma lower_f_of_unitDist {P : Finset ℝ²} {k : ℕ} (hk : 0 < k)
    (h : k * P.card < Erdos.unitDist P) :
    ∃ A : Finset ℝ², A ⊆ P ∧ A.Nonempty ∧
      k ∈ possible_f_values A.card ∧ k ≤ f A.card := by
  classical
  letI : DecidableEq P := Classical.decEq P
  let G := unitGraph P
  have hG : k * Fintype.card P < edgeCount G Finset.univ := by
    rw [edgeCount_univ, show G.edgeFinset.card = Erdos.unitDist P by
      simpa [G] using card_edgeFinset_unitGraph P]
    simpa using h
  obtain ⟨t, ht, htne, htdeg⟩ := core_of_dense G k Finset.univ hG
  let A : Finset ℝ² := t.image Subtype.val
  have hAcard : A.card = t.card := by
    unfold A
    rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
  have hAsub : A ⊆ P := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  have hAne : A.Nonempty := htne.image _
  have hprop : hasMinEquidistantProperty k A := by
    refine ⟨hAne, ?_⟩
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hdeg := htdeg v hv
    let neighbors := (t.erase v).filter fun w => G.Adj v w
    have hneighbors : k ≤ neighbors.card := by
      simpa [neighbors] using hdeg
    have hnne : neighbors.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk hneighbors)
    have himage :
        neighbors.image Subtype.val =
          (A.erase (v : ℝ²)).filter fun w => dist (v : ℝ²) w = 1 := by
      ext w
      constructor
      · intro hw
        rw [Finset.mem_image] at hw
        obtain ⟨u, hu, rfl⟩ := hw
        rw [Finset.mem_filter, Finset.mem_erase] at hu
        rw [Finset.mem_filter, Finset.mem_erase]
        refine ⟨⟨?_, Finset.mem_image_of_mem _ hu.1.2⟩, ?_⟩
        · intro h
          exact hu.1.1 (Subtype.ext h)
        · simpa [G, unitGraph] using hu.2
      · intro hw
        rw [Finset.mem_filter, Finset.mem_erase] at hw
        simp only [A, Finset.mem_image] at hw
        obtain ⟨u, hu, rfl⟩ := hw.1.2
        rw [Finset.mem_image]
        refine ⟨u, ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_erase]
        refine ⟨⟨?_, hu⟩, ?_⟩
        · intro h
          exact hw.1.1 (congrArg Subtype.val h)
        · simpa [G, unitGraph] using hw.2
    have hcard :
        neighbors.card =
          ((A.erase (v : ℝ²)).filter fun w => dist (v : ℝ²) w = 1).card := by
      rw [← himage]
      rw [Finset.card_image_of_injOn Subtype.val_injective.injOn]
    unfold maxEquidistantPointsAt
    apply hneighbors.trans
    rw [hcard]
    apply le_csSup
    · exact (Finset.finite_toSet _).bddAbove
    · rw [Finset.mem_coe, Finset.mem_image]
      refine ⟨1, ?_, rfl⟩
      rw [Finset.mem_image]
      obtain ⟨w, hw⟩ := hnne
      have hwA :
          (w : ℝ²) ∈
            (A.erase (v : ℝ²)).filter fun z => dist (v : ℝ²) z = 1 := by
        rw [← himage]
        exact Finset.mem_image_of_mem _ hw
      rw [Finset.mem_filter] at hwA
      exact ⟨(w : ℝ²), hwA.1, hwA.2⟩
  have hkmem : k ∈ possible_f_values A.card := by
    unfold possible_f_values
    change ∃ (points : Finset ℝ²) (_ : points.card = A.card),
      hasMinEquidistantProperty k points
    exact ⟨A, rfl, hprop⟩
  refine ⟨A, hAsub, hAne, hkmem, ?_⟩
  unfold f
  apply le_csSup
  · exact possible_f_values_BddAbove A.card
  · exact hkmem

lemma contradiction_of_large_unitDist (c : ℝ) (hc : 0 < c) (N n : ℕ)
    (P : Finset ℝ²) (hcard : P.card = n) (hn : 1 < n)
    (hL : 0 < Real.log (Real.log (n : ℝ)))
    (hsmall :
      Real.log (Real.log (n : ℝ)) ≤ c * Real.sqrt (Real.log (n : ℝ)))
    (hSbig :
      max (Real.log 2 + 1) (Real.log (2 * ((N : ℝ) + 1)) + 1) ≤
        Real.sqrt (Real.log (n : ℝ)))
    (hupper : ∀ m : ℕ, N ≤ m →
      (f m : ℝ) ≤ m ^ (c / (m : ℝ).log.log))
    (hedges :
      (n : ℝ) ^ (1 + 4 * c / Real.log (Real.log n)) <
        (Erdos.unitDist P : ℝ)) : False := by
  let L := Real.log (Real.log (n : ℝ))
  let S := Real.sqrt (Real.log (n : ℝ))
  let q := (n : ℝ) ^ (3 * c / L)
  let r := (n : ℝ) ^ (2 * c / L)
  let k := ⌊q⌋₊
  have hLpos : 0 < L := by simpa [L] using hL
  have hlogn : 0 < Real.log (n : ℝ) := by
    have : 1 < Real.log (n : ℝ) := (Real.log_pos_iff (by positivity)).mp hL
    linarith
  have hnR : 1 < (n : ℝ) := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hSsq : S ^ 2 = Real.log (n : ℝ) := by
    dsimp [S]
    rw [Real.sq_sqrt hlogn.le]
  have hratio : S ≤ c * Real.log (n : ℝ) / L := by
    rw [le_div_iff₀ hLpos]
    calc
      S * L ≤ S * (c * S) := by
        gcongr
      _ = c * Real.log (n : ℝ) := by rw [← hSsq]; ring
  have hratio' : S ≤ (c / L) * Real.log (n : ℝ) := by
    calc
      S ≤ c * Real.log (n : ℝ) / L := hratio
      _ = (c / L) * Real.log (n : ℝ) := by ring
  have hSlog2 : Real.log 2 < S := by
    have := le_trans (le_max_left _ _) hSbig
    linarith
  have hSlogN : Real.log (2 * ((N : ℝ) + 1)) < S := by
    have := le_trans (le_max_right _ _) hSbig
    linarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hrpos : 0 < r := by dsimp [r]; positivity
  have h2r_lt_q : 2 * r < q := by
    rw [← Real.log_lt_log_iff (by positivity) hqpos]
    rw [Real.log_mul (by norm_num) hrpos.ne', Real.log_rpow hnpos,
      Real.log_rpow hnpos]
    calc
      Real.log 2 + 2 * c / L * Real.log (n : ℝ)
          = 2 * ((c / L) * Real.log (n : ℝ)) + Real.log 2 := by ring
      _ < 3 * ((c / L) * Real.log (n : ℝ)) := by
        nlinarith [hSlog2.trans_le hratio']
      _ = 3 * c / L * Real.log (n : ℝ) := by ring
  have hconst_lt_q : 2 * ((N : ℝ) + 1) < q := by
    rw [← Real.log_lt_log_iff (by positivity) hqpos]
    rw [Real.log_rpow hnpos]
    calc
      Real.log (2 * ((N : ℝ) + 1)) < S := hSlogN
      _ ≤ (c / L) * Real.log (n : ℝ) := hratio'
      _ ≤ 3 * ((c / L) * Real.log (n : ℝ)) := by
        nlinarith [hSpos, hratio']
      _ = 3 * c / L * Real.log (n : ℝ) := by ring
  have hqfloor : q < (k : ℝ) + 1 := by
    exact Nat.lt_floor_add_one q
  have hrone : 1 < r := by
    have hexp : 0 < 2 * c / L := by positivity
    dsimp [r]
    simpa using Real.rpow_lt_rpow_of_exponent_lt hnR hexp
  have hrk : r < (k : ℝ) := by nlinarith
  have hkpos : 0 < k := by
    exact_mod_cast (lt_trans zero_lt_one hrone |>.trans hrk)
  have hNk : N < k := by
    exact_mod_cast (by nlinarith [hconst_lt_q, hqfloor] :
      (N : ℝ) < k)
  have hkq : (k : ℝ) ≤ q := by
    exact Nat.floor_le hqpos.le
  have hdense : k * P.card < Erdos.unitDist P := by
    have hbase :
        ((k * P.card : ℕ) : ℝ) <
          (n : ℝ) ^ (1 + 4 * c / L) := by
      calc
        ((k * P.card : ℕ) : ℝ) = (n : ℝ) * k := by
          rw [hcard]
          norm_num [mul_comm]
        _ ≤ (n : ℝ) * q := by gcongr
        _ = (n : ℝ) ^ (1 + 3 * c / L) := by
          dsimp [q]
          rw [Real.rpow_add hnpos]
          norm_num
        _ < (n : ℝ) ^ (1 + 4 * c / L) := by
          apply Real.rpow_lt_rpow_of_exponent_lt hnR
          have : 0 < c / L := by positivity
          calc
            1 + 3 * c / L = 1 + 3 * (c / L) := by ring
            _ < 1 + 4 * (c / L) := by nlinarith
            _ = 1 + 4 * c / L := by ring
    have hreal : ((k * P.card : ℕ) : ℝ) < (Erdos.unitDist P : ℝ) :=
      hbase.trans (by simpa [L] using hedges)
    exact_mod_cast hreal
  obtain ⟨A, hAsub, hAne, hkmem, hkf⟩ :=
    lower_f_of_unitDist hkpos hdense
  have hkm : k ≤ A.card := possible_value_le_card hkmem
  have hmle : A.card ≤ n := by
    rw [← hcard]
    exact Finset.card_le_card hAsub
  have hNm : N ≤ A.card := le_trans hNk.le hkm
  have hupperA := hupper A.card hNm
  have hrm : r < (A.card : ℝ) := by
    exact hrk.trans_le (by exact_mod_cast hkm)
  have hlogr : Real.log r = (2 * c / L) * Real.log (n : ℝ) := by
    dsimp [r]
    rw [Real.log_rpow hnpos]
  have hlogm_gt : 2 * S < Real.log (A.card : ℝ) := by
    have hlog_lt := Real.log_lt_log hrpos hrm
    rw [hlogr] at hlog_lt
    have hratio' : 2 * S ≤ (2 * c / L) * Real.log (n : ℝ) := by
      calc
        2 * S ≤ 2 * (c * Real.log (n : ℝ) / L) := by nlinarith
        _ = (2 * c / L) * Real.log (n : ℝ) := by ring
    exact hratio'.trans_lt hlog_lt
  have hlogmpos : 0 < Real.log (A.card : ℝ) :=
    lt_of_lt_of_le (by positivity) hlogm_gt.le
  have hloglogm : L / 2 ≤ Real.log (Real.log (A.card : ℝ)) := by
    have hlog_lt := Real.log_lt_log (by positivity : 0 < 2 * S) hlogm_gt
    rw [Real.log_mul (by norm_num) hSpos.ne', Real.log_sqrt hlogn.le] at hlog_lt
    dsimp [L, S] at hlog_lt ⊢
    linarith [Real.log_pos one_lt_two]
  have hloglogmpos : 0 < Real.log (Real.log (A.card : ℝ)) := by
    linarith
  have hexp_le :
      c / Real.log (Real.log (A.card : ℝ)) ≤ 2 * c / L := by
    rw [div_le_iff₀ hloglogmpos]
    rw [show 2 * c / L * Real.log (Real.log (A.card : ℝ)) =
        (2 * c * Real.log (Real.log (A.card : ℝ))) / L by ring]
    rw [le_div_iff₀ hLpos]
    nlinarith
  have hmone : 1 ≤ (A.card : ℝ) := by
    linarith [hrone, hrm]
  have hr_le :
      (A.card : ℝ) ^ (c / Real.log (Real.log (A.card : ℝ))) ≤ r := by
    calc
      (A.card : ℝ) ^ (c / Real.log (Real.log (A.card : ℝ)))
          ≤ (A.card : ℝ) ^ (2 * c / L) :=
            Real.rpow_le_rpow_of_exponent_le hmone hexp_le
      _ ≤ (n : ℝ) ^ (2 * c / L) := by
        apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast hmle
        · positivity
      _ = r := by rfl
  have hk_le_r : (k : ℝ) ≤ r := by
    calc
      (k : ℝ) ≤ (f A.card : ℝ) := by exact_mod_cast hkf
      _ ≤ (A.card : ℝ) ^ (c / Real.log (Real.log (A.card : ℝ))) := hupperA
      _ ≤ r := hr_le
  exact (not_le_of_gt hrk) hk_le_r

theorem erdos_92.variants.strong : ¬
    ∃ c > 0, ∀ᶠ n in atTop, (f n : ℝ) ≤ n ^ (c / (n : ℝ).log.log) := by
  rintro ⟨c, hc, hupper_event⟩
  obtain ⟨N, hupper⟩ := Filter.eventually_atTop.mp hupper_event
  have hlog_top :
      Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog_top :
      Filter.Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog_top
  have hsqrt_top :
      Filter.Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hlog_top
  have hlittle :
      (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[atTop]
        (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) := by
    have h0 :=
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).comp_tendsto
        hlog_top
    apply h0.congr'
    · exact Filter.Eventually.of_forall fun n => rfl
    · filter_upwards [] with n
      simp [Function.comp_apply, Real.sqrt_eq_rpow]
  have hsmall_event := hlittle.bound hc
  have hLpos_event :
      ∀ᶠ n : ℕ in atTop, 0 < Real.log (Real.log (n : ℝ)) :=
    hloglog_top.eventually (eventually_gt_atTop 0)
  have hSbig_event :
      ∀ᶠ n : ℕ in atTop,
        max (Real.log 2 + 1) (Real.log (2 * ((N : ℝ) + 1)) + 1) ≤
          Real.sqrt (Real.log (n : ℝ)) :=
    hsqrt_top.eventually (eventually_ge_atTop _)
  have hall : ∀ᶠ n : ℕ in atTop,
      1 < n ∧
      0 < Real.log (Real.log (n : ℝ)) ∧
      Real.log (Real.log (n : ℝ)) ≤ c * Real.sqrt (Real.log (n : ℝ)) ∧
      max (Real.log 2 + 1) (Real.log (2 * ((N : ℝ) + 1)) + 1) ≤
        Real.sqrt (Real.log (n : ℝ)) := by
    filter_upwards [hsmall_event, hLpos_event, hSbig_event,
      Filter.eventually_gt_atTop (1 : ℕ)] with n hsmall hL hS hn
    have hloglog_nonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := hL.le
    have hsqrt_nonneg : 0 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_nonneg _
    refine ⟨hn, hL, ?_, hS⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hloglog_nonneg,
      abs_of_nonneg hsqrt_nonneg] using hsmall
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hall
  obtain ⟨n, P, hn, hcard, hedges⟩ :=
    Erdos90b.erdos_90b (4 * c) (by positivity) N₀
  obtain ⟨hn1, hL, hsmall, hSbig⟩ := hN₀ n hn
  exact contradiction_of_large_unitDist c hc N n P hcard hn1 hL hsmall hSbig
    hupper (by simpa [mul_assoc] using hedges)

end Erdos92
