import ErdosProblems.Erdos19.UsefulPairCompression

/-!
# Pair-compression strengthening of the projective-scale argument

The arithmetic and incidence estimates are reused from `Core`; these proofs
retain the disjoint-pair witnesses through every coloring branch.
-/

namespace Erdos19.SetHypergraph

variable {X : Type*}

theorem pairCompressible_of_few_subscale_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r q : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : q * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hsmall : ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard ≤ q)
    (hR : r * (r - 1) ≤ n - 1)
    (hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1) :
    H.PairCompressible n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let A : Set H := {e | e.1.ncard ≤ projectiveScale n}
  let B : Set H := Aᶜ
  have hdisjoint : Disjoint A B := by
    dsimp only [B]
    exact disjoint_compl_right
  have hpartition : A ∪ B = Set.univ := by simp [B]
  have hAweight : ∀ e ∈ A,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hBweight : ∀ e ∈ B,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e heB
    have hek : projectiveScale n + 1 ≤ e.1.ncard := by
      dsimp only [B, A] at heB
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at heB
      omega
    have hscale : n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := by
      have hupper := le_projectiveScale_sq_add n
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := hscale
      _ = (projectiveScale n + 1) * projectiveScale n := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hsurplus : A.ncard + B.ncard - n ≤ A.ncard / 4 :=
    H.partition_surplus_le_quarter_of_pairWeights_pred hlinear n
      (r * (r - 1)) (by omega) hvertices A B hdisjoint hpartition
      hR hquarter hAweight hBweight
  have huseful : ∀ {e : H}, e ∈ A → ∀ {f : H}, f ∈ A →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f := by
    intro e heA f hfA hef hinter
    have hek : e.1.ncard ≤ projectiveScale n := heA
    have hfk : f.1.ncard ≤ projectiveScale n := hfA
    obtain ⟨w, hwe, hwf⟩ := hinter
    by_cases heSmall : e.1.ncard ≤ projectiveScale n - 1
    · exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
        hvertices hr hrhalf hmin e f hef w hwe hwf hek hfk (Or.inl heSmall)
    by_cases hfSmall : f.1.ncard ≤ projectiveScale n - 1
    · exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
        hvertices hr hrhalf hmin e f hef w hwe hwf hek hfk (Or.inr hfSmall)
    have heeq : e.1.ncard = projectiveScale n := by omega
    have hfeq : f.1.ncard = projectiveScale n := by omega
    have hlocal :
        (H.smallIncidentEdges w (projectiveScale n)).ncard ≤ q := by
      apply (Set.ncard_le_ncard (t :=
        ({g : H | g.1.ncard < projectiveScale n} : Set H))
        (fun _g hg ↦ hg.2) (Set.toFinite _)).trans
      exact hsmall
    exact H.isUseful_of_few_small_incident_below_projectiveScale hlinear n r q
      hn hvertices (by omega) hrscale hmin hdefect e f hef w hwe hwf
      heeq hfeq hlocal
  exact H.pairCompressible_of_useful_partition (by omega) A B hdisjoint
    hpartition hsurplus huseful

theorem pairCompressible_of_subscale_volume_balance [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n r : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hR : r * (r - 1) ≤ n - 1)
    (hbalance : 4 *
      (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
          (n - 1 - r * (r - 1)) +
        ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
          (n - 1 - projectiveScale n * (projectiveScale n - 1))) ≤
      (n - 1) *
        ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard) :
    H.PairCompressible n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let Aminus : Set H := {e | e.1.ncard < projectiveScale n}
  let Aplus : Set H := {e | e.1.ncard = projectiveScale n}
  let Bbig : Set H := {e | projectiveScale n < e.1.ncard}
  let Rest : Set H := Aplus ∪ Bbig
  have hmp : Disjoint Aminus Aplus := by
    rw [Set.disjoint_left]
    intro e heminus heplus
    change e.1.ncard < projectiveScale n at heminus
    change e.1.ncard = projectiveScale n at heplus
    omega
  have hmb : Disjoint Aminus Bbig := by
    rw [Set.disjoint_left]
    intro e heminus hebig
    change e.1.ncard < projectiveScale n at heminus
    change projectiveScale n < e.1.ncard at hebig
    omega
  have hpb : Disjoint Aplus Bbig := by
    rw [Set.disjoint_left]
    intro e heplus hebig
    change e.1.ncard = projectiveScale n at heplus
    change projectiveScale n < e.1.ncard at hebig
    omega
  have hthree : (Aminus ∪ Aplus) ∪ Bbig = Set.univ := by
    ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change (e.1.ncard < projectiveScale n ∨
      e.1.ncard = projectiveScale n) ∨ projectiveScale n < e.1.ncard
    omega
  have hAminusWeight : ∀ e ∈ Aminus,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hAplusWeight : ∀ e ∈ Aplus,
      projectiveScale n * (projectiveScale n - 1) ≤
        e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    change e.1.ncard = projectiveScale n at he
    rw [he]
  have hBbigWeight : ∀ e ∈ Bbig,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    have hek : projectiveScale n + 1 ≤ e.1.ncard := by
      change projectiveScale n < e.1.ncard at he
      omega
    have hscale : n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := by
      have hupper := le_projectiveScale_sq_add n
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ projectiveScale n * (projectiveScale n + 1) := hscale
      _ = (projectiveScale n + 1) * projectiveScale n := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hK : projectiveScale n * (projectiveScale n - 1) ≤ n - 1 := by
    have hpred := projectiveScale_pred_sq_add_le (n := n) (by omega)
    have hk : 1 ≤ projectiveScale n := by
      have := two_le_projectiveScale hn
      omega
    have hid : projectiveScale n * (projectiveScale n - 1) =
        (projectiveScale n - 1) * (projectiveScale n - 1) +
          (projectiveScale n - 1) := by
      let j := projectiveScale n - 1
      have hkj : projectiveScale n = j + 1 := by
        dsimp only [j]
        omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hsurplus :
      Aminus.ncard + Aplus.ncard + Bbig.ncard - n ≤ Aminus.ncard / 4 := by
    apply H.triple_partition_surplus_le_quarter_of_pairWeights_pred hlinear n
      (r * (r - 1)) (projectiveScale n * (projectiveScale n - 1))
      (by omega) hvertices Aminus Aplus Bbig hmp hmb hpb hthree hR hK
      hAminusWeight hAplusWeight hBbigWeight
    simpa only [Aminus, Aplus] using hbalance
  have hrestDisjoint : Disjoint Aminus Rest := by
    rw [Set.disjoint_left]
    intro e heminus herest
    rcases herest with heplus | hebig
    · exact Set.disjoint_left.mp hmp heminus heplus
    · exact Set.disjoint_left.mp hmb heminus hebig
  have hrestPartition : Aminus ∪ Rest = Set.univ := by
    dsimp only [Rest]
    rw [← Set.union_assoc]
    exact hthree
  have hRestCard : Rest.ncard = Aplus.ncard + Bbig.ncard := by
    dsimp only [Rest]
    exact Set.ncard_union_eq hpb
  have hsurplus' : Aminus.ncard + Rest.ncard - n ≤ Aminus.ncard / 4 := by
    rw [hRestCard]
    simpa only [Nat.add_assoc] using hsurplus
  have huseful : ∀ {e : H}, e ∈ Aminus → ∀ {f : H}, f ∈ Aminus →
      e ≠ f → (e.1 ∩ f.1).Nonempty → H.IsUseful n e f := by
    intro e he f hf hef hinter
    obtain ⟨w, hwe, hwf⟩ := hinter
    have heSmall : e.1.ncard ≤ projectiveScale n - 1 := by
      change e.1.ncard < projectiveScale n at he
      omega
    have hfSmall : f.1.ncard ≤ projectiveScale n - 1 := by
      change f.1.ncard < projectiveScale n at hf
      omega
    exact H.isUseful_of_one_edge_below_projectiveScale hlinear n r hn
      hvertices hr hrhalf hmin e f hef w hwe hwf
      (heSmall.trans (Nat.sub_le _ _)) (hfSmall.trans (Nat.sub_le _ _))
      (Or.inl heSmall)
  exact H.pairCompressible_of_useful_partition (by omega) Aminus Rest
    hrestDisjoint hrestPartition hsurplus' huseful

theorem pairCompressible_of_projectiveScale_threeway [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r qSmall s qOutside : ℕ)
    (hn : 4 ≤ n) (hvertices : Fintype.card X = n)
    (hr : 2 ≤ r) (hrscale : r ≤ projectiveScale n)
    (hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1))
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hdefect : qSmall * (projectiveScale n - r) ≤ projectiveScale n - 2)
    (hR : r * (r - 1) ≤ n - 1)
    (hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1)
    (hs : 0 < s)
    (houtside : qOutside + s ≤ projectiveScale n + 1)
    (hdensity : ∀ t,
      Fintype.card H = n + t →
      ¬({e : H | e.1.ncard < projectiveScale n} : Set H).ncard ≤ qSmall →
      ¬4 *
          (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - r * (r - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - projectiveScale n * (projectiveScale n - 1))) ≤
        (n - 1) *
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard →
      (n - 1) * t ≤
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - r * (r - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - projectiveScale n * (projectiveScale n - 1)) →
      n <
        (({e : H | e.1.ncard = projectiveScale n} : Set H).ncard -
            ((({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
                  (projectiveScale n - 1) / (qSmall + 1)) *
                ((n - 1) / (projectiveScale n - 1)) / s) -
            4 * (t - 1)) * qOutside) :
    H.PairCompressible n := by
  classical
  let _ : Fintype H := Fintype.ofFinite H
  let k := projectiveScale n
  let Aminus : Set H := {e | e.1.ncard < k}
  let Aplus : Set H := {e | e.1.ncard = k}
  let Bbig : Set H := {e | k < e.1.ncard}
  by_cases hsmallCard : Fintype.card H ≤ n
  · exact H.pairCompressible_of_card_le hsmallCard
  by_cases hfew : Aminus.ncard ≤ qSmall
  · apply H.pairCompressible_of_few_subscale_edges hlinear n r qSmall hn
      hvertices hr hrscale hrhalf hmin hdefect
    · simpa only [Aminus, k] using hfew
    · exact hR
    · exact hquarter
  let lossR := n - 1 - r * (r - 1)
  let lossK := n - 1 - k * (k - 1)
  by_cases hbalance :
      4 * (Aminus.ncard * lossR + Aplus.ncard * lossK) ≤
        (n - 1) * Aminus.ncard
  · apply H.pairCompressible_of_subscale_volume_balance hlinear n r hn
      hvertices hr hrhalf hmin hR
    simpa only [Aminus, Aplus, lossR, lossK, k] using hbalance
  have hmp : Disjoint Aminus Aplus := by
    rw [Set.disjoint_left]
    intro e heminus heplus
    change e.1.ncard < k at heminus
    change e.1.ncard = k at heplus
    omega
  have hmb : Disjoint Aminus Bbig := by
    rw [Set.disjoint_left]
    intro e heminus hebig
    change e.1.ncard < k at heminus
    change k < e.1.ncard at hebig
    omega
  have hpb : Disjoint Aplus Bbig := by
    rw [Set.disjoint_left]
    intro e heplus hebig
    change e.1.ncard = k at heplus
    change k < e.1.ncard at hebig
    omega
  have hpartition : (Aminus ∪ Aplus) ∪ Bbig = Set.univ := by
    ext e
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    change (e.1.ncard < k ∨ e.1.ncard = k) ∨ k < e.1.ncard
    omega
  have hAweight : ∀ e ∈ Aminus,
      r * (r - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e _
    exact Nat.mul_le_mul (hmin e) (Nat.sub_le_sub_right (hmin e) 1)
  have hPweight : ∀ e ∈ Aplus,
      k * (k - 1) ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    change e.1.ncard = k at he
    rw [he]
  have hBweight : ∀ e ∈ Bbig,
      n - 1 ≤ e.1.ncard * (e.1.ncard - 1) := by
    intro e he
    have hek : k + 1 ≤ e.1.ncard := by
      change k < e.1.ncard at he
      omega
    have hscale : n - 1 ≤ k * (k + 1) := by
      have hupper := le_projectiveScale_sq_add n
      dsimp only [k]
      calc
        n - 1 ≤ projectiveScale n * projectiveScale n + projectiveScale n := by
          omega
        _ = projectiveScale n * (projectiveScale n + 1) := by ring
    calc
      n - 1 ≤ k * (k + 1) := hscale
      _ = (k + 1) * k := by ring
      _ ≤ e.1.ncard * (e.1.ncard - 1) :=
        Nat.mul_le_mul hek (Nat.sub_le_sub_right hek 1)
  have hK : k * (k - 1) ≤ n - 1 := by
    have hpred := projectiveScale_pred_sq_add_le (n := n) (by omega)
    have hid : k * (k - 1) = (k - 1) * (k - 1) + (k - 1) := by
      have hkpos : 0 < k := by
        dsimp only [k]
        exact projectiveScale_pos (by omega)
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    simpa only [k] using (show
      (projectiveScale n - 1) * (projectiveScale n - 1) +
        (projectiveScale n - 1) ≤ n - 1 by omega)
  have hweight :
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤ n * (n - 1) := by
    calc
      Aminus.ncard * (r * (r - 1)) + Aplus.ncard * (k * (k - 1)) +
          Bbig.ncard * (n - 1) ≤
          ∑ e : H, e.1.ncard * (e.1.ncard - 1) :=
        H.triple_partition_pairWeight_le Aminus Aplus Bbig hmp hmb hpb
          hpartition (r * (r - 1)) (k * (k - 1)) (n - 1)
          hAweight hPweight hBweight
      _ ≤ Fintype.card X * (Fintype.card X - 1) :=
        H.sum_ncard_mul_sub_one_le hlinear
      _ = n * (n - 1) := by rw [hvertices]
  have hpartsCard : Fintype.card H =
      Aminus.ncard + Aplus.ncard + Bbig.ncard := by
    have hab : (Aminus ∪ Aplus).ncard = Aminus.ncard + Aplus.ncard :=
      Set.ncard_union_eq hmp
    have habb : Disjoint (Aminus ∪ Aplus) Bbig := by
      rw [Set.disjoint_left]
      intro e heab heb
      rcases heab with hea | hep
      · exact Set.disjoint_left.mp hmb hea heb
      · exact Set.disjoint_left.mp hpb hep heb
    calc
      Fintype.card H = (Set.univ : Set H).ncard := by simp
      _ = ((Aminus ∪ Aplus) ∪ Bbig).ncard := by rw [hpartition]
      _ = (Aminus ∪ Aplus).ncard + Bbig.ncard := Set.ncard_union_eq habb
      _ = Aminus.ncard + Aplus.ncard + Bbig.ncard := by rw [hab]
  let t := Fintype.card H - n
  have hcard : Fintype.card H = n + t := by dsimp only [t]; omega
  have hsurplus : (n - 1) * t ≤
      Aminus.ncard * lossR + Aplus.ncard * lossK := by
    have h := weighted_three_surplus_mul_le hR hK hweight
    rw [← hpartsCard] at h
    simpa only [t, lossR, lossK] using h
  have hdensity' : n <
      (Aplus.ncard -
          ((Aminus.ncard * (k - 1) / (qSmall + 1)) *
              ((n - 1) / (k - 1)) / s) -
          4 * (t - 1)) * qOutside := by
    apply hdensity t hcard
    · simpa only [Aminus, k] using hfew
    · simpa only [Aminus, Aplus, lossR, lossK, k] using hbalance
    · simpa only [Aminus, Aplus, lossR, lossK, k] using hsurplus
  apply H.pairCompressible_of_projectiveScale_claim_of_floor_density hlinear
    n r qSmall s qOutside t hn hvertices (by omega) hrscale hmin hdefect
    hcard hs houtside
  simpa only [Aminus, Aplus, k] using hdensity'

theorem pairCompressible_of_fixedFraction_projectiveScale_edges [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (n : ℕ)
    (hvertices : Fintype.card X = n)
    (hk : 65536 ≤ projectiveScale n)
    (hmin : ∀ e : H,
      projectiveScale n - projectiveScale n / 1024 ≤ e.1.ncard) :
    H.PairCompressible n := by
  let k := projectiveScale n
  let u := k / 1024
  let r := k - u
  let qSmall := 512
  let s := k / 8
  let qOutside := k + 1 - s
  have hk' : 65536 ≤ k := by simpa only [k] using hk
  have hn2 : 2 ≤ n := by
    by_contra hnnot
    have htest : n ≤ 1 * 1 + 1 + 1 := by omega
    have hscale_le : projectiveScale n ≤ 1 :=
      Nat.find_min' (exists_projectiveScale n) htest
    omega
  have hlow : (k - 1) * (k - 1) + (k - 1) + 2 ≤ n := by
    simpa only [k] using projectiveScale_pred_sq_add_le (n := n) hn2
  have hup : n ≤ k * k + k + 1 := by
    simpa only [k] using le_projectiveScale_sq_add n
  have hn : 4 ≤ n := by
    have hj : 1 ≤ k - 1 := by omega
    have hmul : 1 * 1 ≤ (k - 1) * (k - 1) := Nat.mul_le_mul hj hj
    norm_num at hmul
    omega
  have hu_mul : 1024 * u ≤ k := by
    dsimp only [u]
    exact Nat.mul_div_le k 1024
  have hu_le : u ≤ k := by
    have hu : u ≤ 1024 * u := by
      simpa [Nat.mul_comm] using
        Nat.mul_le_mul_left u (by norm_num : 1 ≤ 1024)
    exact hu.trans hu_mul
  have hku : k = r + u := by dsimp only [r]; omega
  have hr : 2 ≤ r := by
    have hu4 : 4 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 4 ≤ 1024)).trans hu_mul
    dsimp only [r]
    omega
  have hrscale : r ≤ projectiveScale n := by dsimp only [r, k]; omega
  have hrhalf : projectiveScale n + 1 ≤ 2 * (r - 1) := by
    have hu4 : 4 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 4 ≤ 1024)).trans hu_mul
    dsimp only [r, k]
    omega
  have hmin' : ∀ e : H, r ≤ e.1.ncard := by
    intro e
    simpa only [r, u, k] using hmin e
  have hdiff : projectiveScale n - r = u := by
    dsimp only [r, k]
    omega
  have hdefect : qSmall * (projectiveScale n - r) ≤
      projectiveScale n - 2 := by
    rw [hdiff]
    have h512 : 512 * u ≤ k / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
      calc
        512 * u * 2 = 1024 * u := by ring
        _ ≤ k := hu_mul
    dsimp only [qSmall, k]
    omega
  have hK : k * (k - 1) ≤ n - 1 := by
    have hid : k * (k - 1) =
        (k - 1) * (k - 1) + (k - 1) := by
      let j := k - 1
      have hkj : k = j + 1 := by dsimp only [j]; omega
      rw [hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    rw [hid]
    omega
  have hR : r * (r - 1) ≤ n - 1 := by
    have hrk : r ≤ k := by dsimp only [r]; omega
    exact (Nat.mul_le_mul hrk (Nat.sub_le_sub_right hrk 1)).trans hK
  have hlossR : n - 1 - r * (r - 1) ≤ 2 * k * u + 2 * k := by
    have hpoly : n - 1 ≤ k * k + k := by omega
    have hid : k * k + k + (u * u + u) =
        r * (r - 1) + (2 * k * u + 2 * k) := by
      let j := r - 1
      have hrj : r = j + 1 := by dsimp only [j]; omega
      have hkj : k = j + 1 + u := by omega
      rw [hrj, hkj]
      have hj : j + 1 - 1 = j := by omega
      rw [hj]
      ring
    have hsum : n - 1 ≤ r * (r - 1) + (2 * k * u + 2 * k) := by
      calc
        n - 1 ≤ k * k + k := hpoly
        _ ≤ k * k + k + (u * u + u) := Nat.le_add_right _ _
        _ = r * (r - 1) + (2 * k * u + 2 * k) := hid
    omega
  have hlossR32 : 32 * (n - 1 - r * (r - 1)) ≤ n - 1 := by
    have hu256 : 256 * u ≤ k :=
      (Nat.mul_le_mul_right u (by decide : 256 ≤ 1024)).trans hu_mul
    have h256ku : 256 * k * u ≤ k * k := by
      calc
        256 * k * u = k * (256 * u) := by ring
        _ ≤ k * k := Nat.mul_le_mul_left k hu256
    have h256k : 256 * k ≤ k * k := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k (by omega : 256 ≤ k)
    have hfour : 4 * (64 * k * u + 64 * k) ≤ 2 * (k * k) := by
      calc
        4 * (64 * k * u + 64 * k) = 256 * k * u + 256 * k := by ring
        _ ≤ k * k + k * k := Nat.add_le_add h256ku h256k
        _ = 2 * (k * k) := by ring
    have htwo : 2 * (k * k) ≤ 4 * (k * (k - 1)) := by
      have h2k : 2 * k ≤ 4 * (k - 1) := by omega
      calc
        2 * (k * k) = k * (2 * k) := by ring
        _ ≤ k * (4 * (k - 1)) := Nat.mul_le_mul_left k h2k
        _ = 4 * (k * (k - 1)) := by ring
    have hbase : 64 * k * u + 64 * k ≤ k * (k - 1) :=
      Nat.le_of_mul_le_mul_left (hfour.trans htwo) (by norm_num : 0 < 4)
    calc
      32 * (n - 1 - r * (r - 1)) ≤ 32 * (2 * k * u + 2 * k) :=
        Nat.mul_le_mul_left 32 hlossR
      _ = 64 * k * u + 64 * k := by ring
      _ ≤ k * (k - 1) := hbase
      _ ≤ n - 1 := hK
  have hquarter : 4 * (n - 1 - r * (r - 1)) ≤ n - 1 := by
    have hfour32 :
        4 * (n - 1 - r * (r - 1)) ≤
          32 * (n - 1 - r * (r - 1)) := by omega
    exact hfour32.trans hlossR32
  have hs : 0 < s := by
    dsimp only [s]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 8)).2 (by omega)
  have houtside : qOutside + s ≤ projectiveScale n + 1 := by
    dsimp only [qOutside, s, k]
    omega
  apply H.pairCompressible_of_projectiveScale_threeway hlinear
    n r qSmall s qOutside hn hvertices hr hrscale hrhalf hmin' hdefect
    hR hquarter hs houtside
  intro t _hcard hfew hbalance hsurplus
  have ha : 513 ≤
      ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard := by
    dsimp only [qSmall] at hfew
    omega
  have hbalance' :
      (n - 1) *
          ({e : H | e.1.ncard < projectiveScale n} : Set H).ncard <
        4 *
          (({e : H | e.1.ncard < projectiveScale n} : Set H).ncard *
              (n - 1 - (k - k / 1024) * (k - k / 1024 - 1)) +
            ({e : H | e.1.ncard = projectiveScale n} : Set H).ncard *
              (n - 1 - k * (k - 1))) := by
    simpa only [not_le, r, u, k] using hbalance
  have hdensity := fixedFraction_projectiveScale_floor_density hk' hlow hup
    ha hbalance' hsurplus
  have hq : qSmall + 1 = 513 := by rfl
  rw [hq]
  simpa only [r, u, k, s, qOutside] using hdensity

end Erdos19.SetHypergraph

#print axioms Erdos19.SetHypergraph.pairCompressible_of_few_subscale_edges
#print axioms Erdos19.SetHypergraph.pairCompressible_of_subscale_volume_balance
#print axioms Erdos19.SetHypergraph.pairCompressible_of_projectiveScale_threeway
#print axioms Erdos19.SetHypergraph.pairCompressible_of_fixedFraction_projectiveScale_edges
