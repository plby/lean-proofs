import Mathlib
import ErdosProblems.Erdos697.Erdos697Probability
import ErdosProblems.Erdos696.SubsetProduct
import ErdosProblems.Erdos697.Erdos697Bernoulli

/-!
# Weighted subsets and almost-uniform subset products

The Bernoulli law on a finite prime set, conditional on its cardinality,
is the elementary-symmetric law with odds `p / (1-p)`.  This file compares
that law with independent draws from its one-coordinate weighted residue
distribution.  The factorial loss from ordering a subset is kept exactly;
the exponential series then sums all cardinality strata without losing the
sharp `log 2` constant.
-/

open scoped BigOperators

namespace Erdos697.WeightedSubset

noncomputable section

/-! ## Pushing product weights through a finite map -/

theorem sum_tuple_pushforward
    {I G : Type*} [Fintype I] [Fintype G] [DecidableEq G]
    (w : I → ℝ) (f : I → G) {K : ℕ} (H : (Fin K → G) → ℝ) :
    (∑ v : Fin K → I, (∏ j, w (v j)) * H (fun j ↦ f (v j))) =
      ∑ g : Fin K → G,
        (∏ j, ∑ i, if f i = g j then w i else 0) * H g := by
  induction K with
  | zero =>
      simp
      exact congrArg H (Subsingleton.elim _ _)
  | succ K ih =>
      rw [Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (K + 1) ↦ I)).symm
        (fun v : Fin (K + 1) → I =>
          (∏ j, w (v j)) * H (fun j ↦ f (v j)))
        (fun p : I × (Fin K → I) =>
          (∏ j, w ((Fin.cons p.1 p.2 : Fin (K + 1) → I) j)) *
            H (fun j ↦ f ((Fin.cons p.1 p.2 : Fin (K + 1) → I) j))) (by
          intro v
          simp [Fin.cons_self_tail])]
      rw [Fintype.sum_equiv
        (Fin.consEquiv (fun _ : Fin (K + 1) ↦ G)).symm
        (fun g : Fin (K + 1) → G =>
          (∏ j, ∑ i, if f i = g j then w i else 0) * H g)
        (fun p : G × (Fin K → G) =>
          (∏ j, ∑ i,
              if f i = (Fin.cons p.1 p.2 : Fin (K + 1) → G) j then w i else 0) *
            H (Fin.cons p.1 p.2 : Fin (K + 1) → G)) (by
          intro g
          simp [Fin.cons_self_tail])]
      rw [Fintype.sum_prod_type]
      simp_rw [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [Fintype.sum_prod_type]
      simp_rw [mul_assoc]
      have hcons (i : I) (v : Fin K → I) :
          (fun j ↦ f ((Fin.cons i v : Fin (K + 1) → I) j)) =
            Fin.cons (f i) (fun j ↦ f (v j)) := by
        funext j
        refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
      simp_rw [hcons]
      have htail (i : I) :
          (∑ v : Fin K → I,
              (∏ j, w (v j)) *
                H (Fin.cons (f i) (fun j ↦ f (v j)))) =
            ∑ g : Fin K → G,
              (∏ j, ∑ i, if f i = g j then w i else 0) *
                H (Fin.cons (f i) g) :=
        ih (fun g => H (Fin.cons (f i) g))
      calc
        ∑ i : I, ∑ v : Fin K → I,
            w i * ((∏ j, w (v j)) *
              H (Fin.cons (f i) (fun j ↦ f (v j)))) =
            ∑ i : I, w i *
              ∑ v : Fin K → I,
                (∏ j, w (v j)) *
                  H (Fin.cons (f i) (fun j ↦ f (v j))) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (Finset.mul_sum (s := Finset.univ) (a := w i)
            (f := fun v : Fin K → I =>
              (∏ j, w (v j)) *
                H (Fin.cons (f i) (fun j ↦ f (v j))))).symm
        _ = ∑ i : I, w i *
            ∑ g : Fin K → G,
              (∏ j, ∑ i, if f i = g j then w i else 0) *
                H (Fin.cons (f i) g) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [htail i]
        _ = ∑ i : I, ∑ g : Fin K → G,
              w i * ((∏ j, ∑ i, if f i = g j then w i else 0) *
                H (Fin.cons (f i) g)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ =
            ∑ g : Fin K → G, ∑ i : I,
              w i * ((∏ j, ∑ i, if f i = g j then w i else 0) *
                H (Fin.cons (f i) g)) := by
          rw [Finset.sum_comm]
        _ = ∑ g : Fin K → G,
            (∏ j, ∑ i, if f i = g j then w i else 0) *
              ∑ a : G, (∑ i, if f i = a then w i else 0) *
                H (Fin.cons a g) := by
          apply Finset.sum_congr rfl
          intro g _
          let P : ℝ := ∏ j, ∑ i, if f i = g j then w i else 0
          have hfiber :
              (∑ i : I, w i * H (Fin.cons (f i) g)) =
                ∑ a : G, (∑ i, if f i = a then w i else 0) *
                  H (Fin.cons a g) := by
            calc
              (∑ i : I, w i * H (Fin.cons (f i) g)) =
                  ∑ a : G, ∑ i ∈ (Finset.univ : Finset I) with f i = a,
                    w i * H (Fin.cons (f i) g) := by
                exact (Finset.sum_fiberwise (Finset.univ : Finset I) f
                  (fun i => w i * H (Fin.cons (f i) g))).symm
              _ = ∑ a : G, (∑ i, if f i = a then w i else 0) *
                    H (Fin.cons a g) := by
                apply Finset.sum_congr rfl
                intro a _
                rw [Finset.sum_mul]
                simp only [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro i _
                by_cases hi : f i = a
                · simp [hi]
                · simp [hi]
          change (∑ i : I, w i * (P * H (Fin.cons (f i) g))) =
            P * ∑ a : G, (∑ i, if f i = a then w i else 0) *
              H (Fin.cons a g)
          calc
            (∑ i : I, w i * (P * H (Fin.cons (f i) g))) =
                P * ∑ i : I, w i * H (Fin.cons (f i) g) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = _ := by rw [hfiber]
        _ = ∑ a : G, ∑ g : Fin K → G,
            ((∑ i, if f i = a then w i else 0) *
              ∏ j, ∑ i, if f i = g j then w i else 0) *
                H (Fin.cons a g) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          ring
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro g _
          ring

/-! ## Enumerating a fixed-cardinality subset -/

section Enumeration

variable {I : Type*} [Fintype I] [LinearOrder I]

private def enumeration {K : ℕ}
    (x : {S : Finset I // S.card = K} × Equiv.Perm (Fin K)) : Fin K → I :=
  fun j => x.1.1.orderEmbOfFin x.1.2 (x.2 j)

private theorem enumeration_injective {K : ℕ} :
    Function.Injective (enumeration (I := I) (K := K)) := by
  intro x y hxy
  have hrange (z : {S : Finset I // S.card = K} × Equiv.Perm (Fin K)) :
      Finset.image (enumeration z) Finset.univ = z.1.1 := by
    calc
      Finset.image (enumeration z) Finset.univ =
          Finset.image (z.1.1.orderEmbOfFin z.1.2)
            (Finset.image z.2 Finset.univ) := by
        rw [← Finset.image_comp]
        rfl
      _ = Finset.image (z.1.1.orderEmbOfFin z.1.2) Finset.univ := by
        congr 1
        ext j
        simp
      _ = z.1.1 := Finset.image_orderEmbOfFin_univ _ _
  have hSval : x.1.1 = y.1.1 := by
    rw [← hrange x, ← hrange y, hxy]
  have hS : x.1 = y.1 := Subtype.ext hSval
  apply Prod.ext hS
  apply Equiv.ext
  intro j
  apply (x.1.1.orderEmbOfFin x.1.2).injective
  simpa only [enumeration, hS] using congrFun hxy j

private theorem prod_enumeration {K : ℕ} (w : I → ℝ)
    (x : {S : Finset I // S.card = K} × Equiv.Perm (Fin K)) :
    (∏ j, w (enumeration x j)) = ∏ i ∈ x.1.1, w i := by
  unfold enumeration
  calc
    (∏ j, w (x.1.1.orderEmbOfFin x.1.2 (x.2 j))) =
        ∏ j, w (x.1.1.orderEmbOfFin x.1.2 j) := by
      exact Fintype.prod_equiv x.2
        (fun j => w (x.1.1.orderEmbOfFin x.1.2 (x.2 j)))
        (fun j => w (x.1.1.orderEmbOfFin x.1.2 j)) (fun _ => rfl)
    _ = ∏ i ∈ x.1.1, w i := by
      rw [← Finset.prod_image
        (s := (Finset.univ : Finset (Fin K)))
        (g := x.1.1.orderEmbOfFin x.1.2)
        (f := w) (x.1.1.orderEmbOfFin x.1.2).injective.injOn]
      rw [Finset.image_orderEmbOfFin_univ]

theorem factorial_mul_sum_subsets_le_sum_tuples
    {K : ℕ} (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (Pset : Finset I → Prop) [DecidablePred Pset]
    (Ptuple : (Fin K → I) → Prop) [DecidablePred Ptuple]
    (hlift : ∀ S : {S : Finset I // S.card = K}, Pset S.1 →
      ∀ σ : Equiv.Perm (Fin K), Ptuple (enumeration (S, σ))) :
    (K.factorial : ℝ) *
        (∑ S ∈ (Finset.univ : Finset (Finset I)).filter
          (fun S => S.card = K ∧ Pset S), ∏ i ∈ S, w i) ≤
      ∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter Ptuple,
        ∏ j, w (v j) := by
  classical
  let A := {S : Finset I // S.card = K}
  let E : A × Equiv.Perm (Fin K) → (Fin K → I) := enumeration
  let D : Finset (A × Equiv.Perm (Fin K)) :=
    Finset.univ.filter fun x => Pset x.1.1
  have hE : Function.Injective E := enumeration_injective
  have himage : Finset.image E D ⊆
      (Finset.univ : Finset (Fin K → I)).filter Ptuple := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hlift x.1 (by simpa [D] using hx) x.2
  have hnonneg : ∀ v ∈ (Finset.univ : Finset (Fin K → I)).filter Ptuple,
      v ∉ Finset.image E D → 0 ≤ ∏ j, w (v j) := by
    intro v _ _
    exact Finset.prod_nonneg fun j _ => hw (v j)
  calc
    (K.factorial : ℝ) *
        (∑ S ∈ (Finset.univ : Finset (Finset I)).filter
          (fun S => S.card = K ∧ Pset S), ∏ i ∈ S, w i) =
      ∑ x : A × Equiv.Perm (Fin K),
        if Pset x.1.1 then ∏ j, w (enumeration x j) else 0 := by
      simp only [Fintype.sum_prod_type, prod_enumeration,
        Finset.sum_const, nsmul_eq_mul, Fintype.card_perm,
        Fintype.card_fin]
      rw [← Finset.mul_sum]
      congr 1
      · norm_cast
        simpa only [Finset.card_univ, Fintype.card_fin] using
          (Fintype.card_perm (α := Fin K)).symm
      · have hsub :
            (∑ S ∈ (Finset.univ : Finset (Finset I)).filter
                (fun S => S.card = K),
                if Pset S then ∏ i ∈ S, w i else 0) =
              ∑ i : A, if Pset i.1 then ∏ j ∈ i.1, w j else 0 :=
            Finset.sum_subtype
              ((Finset.univ : Finset (Finset I)).filter fun S => S.card = K)
              (fun S => by simp)
              (fun S : Finset I =>
                if Pset S then ∏ i ∈ S, w i else 0)
        calc
          (∑ S ∈ (Finset.univ : Finset (Finset I)).filter
              (fun S => S.card = K ∧ Pset S), ∏ i ∈ S, w i) =
              ∑ S ∈ (Finset.univ : Finset (Finset I)).filter
                (fun S => S.card = K),
                if Pset S then ∏ i ∈ S, w i else 0 := by
            simp only [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro S _
            by_cases hcard : S.card = K <;>
              by_cases hP : Pset S <;> simp [hcard, hP]
          _ = ∑ i : A, if Pset i.1 then ∏ j ∈ i.1, w j else 0 := hsub
    _ = ∑ x ∈ D, ∏ j, w (enumeration x j) := by
      simp only [D, Finset.sum_filter]
    _ = ∑ v ∈ Finset.image E D, ∏ j, w (v j) := by
      simpa only [E] using
        (Finset.sum_image (s := D) (g := E)
          (f := fun v : Fin K → I => ∏ j, w (v j)) hE.injOn).symm
    _ ≤ ∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter Ptuple,
        ∏ j, w (v j) :=
      Finset.sum_le_sum_of_subset_of_nonneg himage hnonneg

end Enumeration

/-! ## Almost-uniform residue tuples -/

section AlmostUniform

variable {I G : Type*} [Fintype I] [Fintype G] [Nonempty G]
  [DecidableEq G]

def residueMass (w : I → ℝ) (f : I → G) (g : G) : ℝ :=
  ∑ i, if f i = g then w i else 0

theorem sum_residueMass (w : I → ℝ) (f : I → G) :
    (∑ g, residueMass w f g) = ∑ i, w i := by
  unfold residueMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sum_tuple_event_le_of_residue_l1
    (w : I → ℝ) (f : I → G) (hw : ∀ i, 0 ≤ w i)
    {W ε B : ℝ} (hW : W = ∑ i, w i) (hWpos : 0 < W)
    (hTV : (∑ g : G,
      |residueMass w f g / W - 1 / (Fintype.card G : ℝ)|) ≤ ε)
    {K : ℕ} (P : (Fin K → G) → Prop) [DecidablePred P]
    (hUniform :
      (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
        1 / (Fintype.card G : ℝ) ^ K) ≤ B) :
    (∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter
        (fun v => P (fun j => f (v j))), ∏ j, w (v j)) ≤
      W ^ K * (B + (K : ℝ) * ε) := by
  classical
  let q : G → ℝ := fun g => residueMass w f g / W
  let u : G → ℝ := fun _ => 1 / (Fintype.card G : ℝ)
  have hmass_nonneg (g : G) : 0 ≤ residueMass w f g := by
    unfold residueMass
    exact Finset.sum_nonneg fun i _ => by
      by_cases hi : f i = g
      · simp [hi, hw i]
      · simp [hi]
  have hq_nonneg (g : G) : 0 ≤ q g :=
    div_nonneg (hmass_nonneg g) hWpos.le
  have hq_sum : (∑ g, q g) = 1 := by
    dsimp [q]
    rw [← Finset.sum_div, sum_residueMass, ← hW]
    exact div_self hWpos.ne'
  have hcardpos : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hu_nonneg (g : G) : 0 ≤ u g := by
    dsimp [u]
    positivity
  have hu_sum : (∑ g, u g) = 1 := by
    simp only [u, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hprodTV :
      (∑ gvec : Fin K → G,
        |(∏ j, q (gvec j)) - (∏ j, u (gvec j))|) ≤
          (K : ℝ) * ε := by
    apply Probability.prod_tv_le_sum_tv (fun _ => q) u
      hu_nonneg hu_sum (fun _ => hq_nonneg) (fun _ => hq_sum) ε
    intro _
    simpa [q, u] using hTV
  have hqEvent :
      (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
          ∏ j, q (g j)) ≤ B + (K : ℝ) * ε := by
    calc
      (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
          ∏ j, q (g j)) ≤
          (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
            ((∏ j, u (g j)) +
              |(∏ j, q (g j)) - (∏ j, u (g j))|)) := by
        apply Finset.sum_le_sum
        intro g _
        linarith [le_abs_self ((∏ j, q (g j)) - (∏ j, u (g j)))]
      _ = (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
            ∏ j, u (g j)) +
          ∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter P,
            |(∏ j, q (g j)) - (∏ j, u (g j))| := by
        rw [Finset.sum_add_distrib]
      _ ≤ B + (K : ℝ) * ε := by
        apply add_le_add
        · simpa [u, Finset.prod_const] using hUniform
        · exact (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun _ _ _ => abs_nonneg _)).trans hprodTV
  have hpush := sum_tuple_pushforward w f
    (K := K) (fun g => if P g then 1 else 0)
  have hleft :
      (∑ v : Fin K → I,
          (∏ j, w (v j)) *
            (if P (fun j => f (v j)) then 1 else 0)) =
        ∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter
          (fun v => P (fun j => f (v j))), ∏ j, w (v j) := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> ring
  have hright :
      (∑ g : Fin K → G,
          (∏ j, residueMass w f (g j)) * (if P g then 1 else 0)) =
        W ^ K * ∑ g ∈
          (Finset.univ : Finset (Fin K → G)).filter P,
            ∏ j, q (g j) := by
    have hmassq (g : G) : residueMass w f g = W * q g := by
      dsimp [q]
      field_simp [hWpos.ne']
    simp_rw [hmassq, Finset.prod_mul_distrib, Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    simp only [Finset.sum_filter]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> ring
  rw [hleft] at hpush
  change (∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter
      (fun v => P (fun j => f (v j))), ∏ j, w (v j)) =
    ∑ g : Fin K → G,
      (∏ j, residueMass w f (g j)) * (if P g then 1 else 0) at hpush
  rw [hright] at hpush
  rw [hpush]
  exact mul_le_mul_of_nonneg_left hqEvent (pow_nonneg hWpos.le K)

end AlmostUniform

/-! ## The two subset-product events used in the density argument -/

section SubsetProductEvents

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

def noRelationTuple {K : ℕ} (g : Fin K → G) : Prop :=
  ∀ S : Finset (Fin K), S.Nonempty → Erdos696.subsetProd S g ≠ 1

def hitsTuple {K : ℕ} (B : Finset G) (g : Fin K → G) : Prop :=
  ∃ S : Finset (Fin K), S.Nonempty ∧ Erdos696.subsetProd S g ∈ B

noncomputable def noRelationTuples (K : ℕ) : Finset (Fin K → G) := by
  classical
  exact Finset.univ.filter noRelationTuple

noncomputable def hittingTuples (K : ℕ) (B : Finset G) : Finset (Fin K → G) := by
  classical
  exact Finset.univ.filter (hitsTuple B)

theorem uniform_noRelationTuple_le {K : ℕ} (hK : 1 ≤ K) :
    (∑ g ∈ noRelationTuples (G := G) K,
      1 / (Fintype.card G : ℝ) ^ K) ≤
        (Fintype.card G : ℝ) / ((2 : ℝ) ^ K - 1) := by
  classical
  have hNpos : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hsum :
      (∑ _g : Fin K → G, 1 / (Fintype.card G : ℝ) ^ K) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have h := Erdos696.subset_product_near_uniform (G := G) hK 0 (by norm_num)
    (fun _ : Fin K → G => 1 / (Fintype.card G : ℝ) ^ K)
    (fun _ => by positivity) hsum (by simp)
  have hevent : noRelationTuples (G := G) K =
      (Finset.univ : Finset (Fin K → G)).filter
        (fun g => ∀ S : Finset (Fin K), S.Nonempty →
          Erdos696.subsetProd S g ≠ 1) := by
    ext g
    simp [noRelationTuples, noRelationTuple]
  rw [hevent]
  simpa only [zero_mul, mul_zero, add_zero] using h

theorem uniform_hitsTuple_le {K : ℕ} (hK : 1 ≤ K) (B : Finset G) :
    (∑ g ∈ hittingTuples (G := G) K B,
      1 / (Fintype.card G : ℝ) ^ K) ≤
        (B.card : ℝ) * ((2 : ℝ) ^ K - 1) /
          (Fintype.card G : ℝ) := by
  classical
  let N : ℝ := Fintype.card G
  let subs := (Finset.univ : Finset (Finset (Fin K))).filter
    fun S => S.Nonempty
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := G)
  have hfiber (S : Finset (Fin K)) (hS : S.Nonempty) (a : G) :
      (∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter
          (fun g => Erdos696.subsetProd S g = a), 1 / N ^ K) = 1 / N := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Erdos696.subsetProd_uniform S hS a]
    dsimp [N]
    have hNne : (Fintype.card G : ℝ) ≠ 0 := by positivity
    have hKpos : 0 < K := by omega
    push_cast
    have hpow : (Fintype.card G : ℝ) ^ K =
        (Fintype.card G : ℝ) ^ (K - 1) * Fintype.card G := by
      rw [← pow_succ, Nat.sub_add_cancel hK]
    rw [hpow]
    field_simp
  have hpoint (g : Fin K → G) (hg : hitsTuple B g) :
      1 / N ^ K ≤
        ∑ S ∈ subs, ∑ a ∈ B,
          if Erdos696.subsetProd S g = a then 1 / N ^ K else 0 := by
    obtain ⟨S, hSne, hSB⟩ := hg
    have hSmem : S ∈ subs := by simp [subs, hSne]
    have hterm :
        (if Erdos696.subsetProd S g = Erdos696.subsetProd S g
          then 1 / N ^ K else 0) = 1 / N ^ K := by simp
    calc
      1 / N ^ K =
          if Erdos696.subsetProd S g = Erdos696.subsetProd S g
            then 1 / N ^ K else 0 := hterm.symm
      _ ≤ ∑ a ∈ B,
          if Erdos696.subsetProd S g = a then 1 / N ^ K else 0 := by
        apply Finset.single_le_sum (s := B)
          (f := fun a => if Erdos696.subsetProd S g = a then 1 / N ^ K else 0)
        · intro a ha
          split_ifs <;> positivity
        · exact hSB
      _ ≤ ∑ S ∈ subs, ∑ a ∈ B,
          if Erdos696.subsetProd S g = a then 1 / N ^ K else 0 := by
        apply Finset.single_le_sum (s := subs)
          (f := fun S => ∑ a ∈ B,
            if Erdos696.subsetProd S g = a then 1 / N ^ K else 0)
        · intro T hT
          exact Finset.sum_nonneg fun a ha => by split_ifs <;> positivity
        · exact hSmem
  calc
    (∑ g ∈ hittingTuples (G := G) K B,
        1 / (Fintype.card G : ℝ) ^ K) =
        ∑ g ∈ hittingTuples (G := G) K B,
          1 / N ^ K := by rfl
    _ ≤ ∑ g : Fin K → G, ∑ S ∈ subs, ∑ a ∈ B,
          if Erdos696.subsetProd S g = a then 1 / N ^ K else 0 := by
      calc
        _ ≤ ∑ g ∈ hittingTuples (G := G) K B,
            ∑ S ∈ subs, ∑ a ∈ B,
              if Erdos696.subsetProd S g = a then 1 / N ^ K else 0 := by
          exact Finset.sum_le_sum fun g hg => hpoint g (by
            simpa [hittingTuples] using hg)
        _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (by intro g hg; simp)
          intro g _ _
          exact Finset.sum_nonneg fun S hS =>
            Finset.sum_nonneg fun a ha => by split_ifs <;> positivity
    _ = ∑ S ∈ subs, ∑ a ∈ B,
          ∑ g ∈ (Finset.univ : Finset (Fin K → G)).filter
            (fun g => Erdos696.subsetProd S g = a), 1 / N ^ K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_comm]
      simp only [Finset.sum_filter]
    _ = ∑ S ∈ subs, ∑ _a ∈ B, 1 / N := by
      apply Finset.sum_congr rfl
      intro S hS
      have hSne : S.Nonempty := by simpa [subs] using hS
      apply Finset.sum_congr rfl
      intro a _
      exact hfiber S hSne a
    _ = (B.card : ℝ) * ((2 : ℝ) ^ K - 1) /
          (Fintype.card G : ℝ) := by
      have hsubcard : subs.card = 2 ^ K - 1 := by
        rw [show subs = (Finset.univ : Finset (Finset (Fin K))) \ {∅} by
          ext S
          simp [subs, Finset.nonempty_iff_ne_empty]]
        rw [Finset.card_sdiff]
        simp
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hsubcard]
      have hpowone : 1 ≤ 2 ^ K :=
        (Nat.pow_pos (by omega : 0 < 2))
      rw [Nat.cast_sub hpowone]
      push_cast
      dsimp [N]
      ring

def noRelationSet {I : Type*} (f : I → G) (S : Finset I) : Prop :=
  ∀ T : Finset I, T ⊆ S → T.Nonempty → (∏ i ∈ T, f i) ≠ 1

noncomputable def noRelationSubsets {I : Type*} [Fintype I]
    (f : I → G) (K : ℕ) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S => S.card = K ∧ noRelationSet f S

/-- Weighted no-relation subsets of a fixed cardinality are controlled by
the corresponding almost-uniform independent residue tuples. -/
theorem factorial_mul_noRelationSet_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℝ) (f : I → G) (hw : ∀ i, 0 ≤ w i)
    {W ε : ℝ} (hW : W = ∑ i, w i) (hWpos : 0 < W)
    (hTV : (∑ g : G,
      |residueMass w f g / W - 1 / (Fintype.card G : ℝ)|) ≤ ε)
    {K : ℕ} (hK : 1 ≤ K) :
    (K.factorial : ℝ) *
        (∑ S ∈ noRelationSubsets f K, ∏ i ∈ S, w i) ≤
      W ^ K *
        ((Fintype.card G : ℝ) / ((2 : ℝ) ^ K - 1) + (K : ℝ) * ε) := by
  classical
  let Ptuple : (Fin K → I) → Prop :=
    fun v => noRelationTuple (fun j => f (v j))
  have hlift :
      (K.factorial : ℝ) *
          (∑ S ∈ noRelationSubsets f K, ∏ i ∈ S, w i) ≤
        ∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter Ptuple,
          ∏ j, w (v j) := by
    have hraw := factorial_mul_sum_subsets_le_sum_tuples w hw
      (noRelationSet f) Ptuple (by
        intro S hS σ
        intro A hA hprod
        let e : Fin K → I := enumeration (S, σ)
        have heinj : Function.Injective e := by
          intro i j hij
          apply σ.injective
          exact (S.1.orderEmbOfFin S.2).injective hij
        let T := Finset.image e A
        have hTS : T ⊆ S.1 := by
          intro i hi
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
          exact S.1.orderEmbOfFin_mem S.2 (σ j)
        have hTne : T.Nonempty := (Finset.image_nonempty.mpr hA)
        have hprodEq : (∏ i ∈ T, f i) =
            Erdos696.subsetProd A (fun j => f (e j)) := by
          unfold Erdos696.subsetProd
          exact Finset.prod_image heinj.injOn
        exact (hS T hTS hTne) (hprodEq.trans hprod))
    have hevent : noRelationSubsets f K =
        (Finset.univ : Finset (Finset I)).filter
          (fun S => S.card = K ∧ noRelationSet f S) := by
      ext S
      simp [noRelationSubsets]
    rw [hevent]
    exact hraw
  have htuple := sum_tuple_event_le_of_residue_l1 w f hw hW hWpos hTV
    (P := noRelationTuple)
    (B := (Fintype.card G : ℝ) / ((2 : ℝ) ^ K - 1))
    (uniform_noRelationTuple_le (G := G) hK)
  exact hlift.trans (by simpa [Ptuple] using htuple)

theorem sum_pow_div_factorial_le_exp (W : ℝ) (hW : 0 ≤ W) (s : Finset ℕ) :
    (∑ k ∈ s, W ^ k / (k.factorial : ℝ)) ≤ Real.exp W := by
  have hexp := NormedSpace.expSeries_div_hasSum_exp W
  rw [Real.exp_eq_exp_ℝ, ← hexp.tsum_eq]
  exact hexp.summable.sum_le_tsum s fun k hk => by positivity

/-- Summing the fixed-cardinality estimate over a bounded cardinality
window costs only the exponential-series factor `exp W`. -/
theorem sum_noRelation_odds_card_range_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℝ) (f : I → G) (hw : ∀ i, 0 ≤ w i)
    {W ε : ℝ} (hW : W = ∑ i, w i) (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass w f g / W - 1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax) :
    (∑ k ∈ Finset.Icc Kmin Kmax,
        ∑ S ∈ noRelationSubsets f k, ∏ i ∈ S, w i) ≤
      Real.exp W *
        ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
          (Kmax : ℝ) * ε) := by
  have hNpos : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hdenpos : 0 < (2 : ℝ) ^ Kmin - 1 := by
    have htwo : (2 : ℝ) ≤ 2 ^ Kmin := by
      calc
        (2 : ℝ) = 2 ^ 1 := (pow_one _).symm
        _ ≤ 2 ^ Kmin := pow_le_pow_right₀ one_le_two hKmin
    linarith
  have hBnonneg : 0 ≤
      (Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
        (Kmax : ℝ) * ε :=
    add_nonneg (div_nonneg hNpos.le hdenpos.le) (mul_nonneg (by positivity) hε)
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc Kmin Kmax) :
      (∑ S ∈ noRelationSubsets f k, ∏ i ∈ S, w i) ≤
        (W ^ k / (k.factorial : ℝ)) *
          ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
            (Kmax : ℝ) * ε) := by
    have hkmin : Kmin ≤ k := (Finset.mem_Icc.mp hk).1
    have hkmax : k ≤ Kmax := (Finset.mem_Icc.mp hk).2
    have hkone : 1 ≤ k := hKmin.trans hkmin
    have hfixed := factorial_mul_noRelationSet_le w f hw hW hWpos hTV hkone
    have hpowmono : (2 : ℝ) ^ Kmin ≤ 2 ^ k :=
      pow_le_pow_right₀ one_le_two hkmin
    have hdenmono : (2 : ℝ) ^ Kmin - 1 ≤ 2 ^ k - 1 := by linarith
    have hdenposk : 0 < (2 : ℝ) ^ k - 1 := hdenpos.trans_le hdenmono
    have hfrac : (Fintype.card G : ℝ) / ((2 : ℝ) ^ k - 1) ≤
        (Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) := by
      exact div_le_div_of_nonneg_left hNpos.le hdenpos hdenmono
    have hkcast : (k : ℝ) ≤ Kmax := by exact_mod_cast hkmax
    have hsmall :
        (Fintype.card G : ℝ) / ((2 : ℝ) ^ k - 1) + (k : ℝ) * ε ≤
          (Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
            (Kmax : ℝ) * ε := by
      exact add_le_add hfrac (mul_le_mul_of_nonneg_right hkcast hε)
    have hfacpos : (0 : ℝ) < k.factorial := by positivity
    calc
      (∑ S ∈ noRelationSubsets f k, ∏ i ∈ S, w i) ≤
          W ^ k / (k.factorial : ℝ) *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ k - 1) +
              (k : ℝ) * ε) := by
        rw [show W ^ k / (k.factorial : ℝ) *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ k - 1) +
              (k : ℝ) * ε) =
            (W ^ k * ((Fintype.card G : ℝ) / ((2 : ℝ) ^ k - 1) +
              (k : ℝ) * ε)) / (k.factorial : ℝ) by ring]
        exact (le_div_iff₀ hfacpos).2 (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hfixed)
      _ ≤ (W ^ k / (k.factorial : ℝ)) *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
              (Kmax : ℝ) * ε) := by
        exact mul_le_mul_of_nonneg_left hsmall (by positivity)
  calc
    (∑ k ∈ Finset.Icc Kmin Kmax,
        ∑ S ∈ noRelationSubsets f k, ∏ i ∈ S, w i) ≤
        ∑ k ∈ Finset.Icc Kmin Kmax,
          (W ^ k / (k.factorial : ℝ)) *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
              (Kmax : ℝ) * ε) := Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Icc Kmin Kmax,
          W ^ k / (k.factorial : ℝ)) *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
              (Kmax : ℝ) * ε) := by rw [Finset.sum_mul]
    _ ≤ Real.exp W *
            ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
              (Kmax : ℝ) * ε) :=
      mul_le_mul_of_nonneg_right
        (sum_pow_div_factorial_le_exp W hWpos.le _) hBnonneg

/-- Bernoulli form of the preceding odds estimate. -/
noncomputable def noRelationCardRange
    {I : Type*} [Fintype I] (f : I → G) (Kmin Kmax : ℕ) :
    Finset (Finset I) := by
  classical
  exact Finset.univ.filter
    (fun S => Kmin ≤ S.card ∧ S.card ≤ Kmax ∧ noRelationSet f S)

theorem sum_weight_noRelation_card_range_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (p : I → ℝ) (f : I → G)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    {W ε : ℝ} (hW : W = ∑ i, Bernoulli.odds p i)
    (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass (Bernoulli.odds p) f g / W -
        1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax) :
    (∑ S ∈ noRelationCardRange f Kmin Kmax,
          Bernoulli.weight Finset.univ p S) ≤
      Bernoulli.zeroBase (Finset.univ : Finset I) p * Real.exp W *
        ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
          (Kmax : ℝ) * ε) := by
  classical
  let z := Bernoulli.zeroBase (Finset.univ : Finset I) p
  have hw0 (i : I) : 0 ≤ Bernoulli.odds p i := by
    unfold Bernoulli.odds
    exact div_nonneg (hp0 i) (sub_nonneg.mpr (hp1 i).le)
  have hz0 : 0 ≤ z := Bernoulli.zeroBase_nonneg _ _
    (fun i _ => (hp1 i).le)
  have hz1 : z ≤ 1 := Bernoulli.zeroBase_le_one _ _
    (fun i _ => hp0 i) (fun i _ => (hp1 i).le)
  have hraw := sum_noRelation_odds_card_range_le
    (Bernoulli.odds p) f hw0 hW hWpos hε hTV hKmin hKK
  have heq :
      (∑ S ∈ noRelationCardRange f Kmin Kmax,
            Bernoulli.weight Finset.univ p S) =
        z * ∑ k ∈ Finset.Icc Kmin Kmax,
          ∑ S ∈ noRelationSubsets f k,
            ∏ i ∈ S, Bernoulli.odds p i := by
    let pairs : Finset (Σ _k : ℕ, Finset I) :=
      (Finset.Icc Kmin Kmax).sigma fun k => noRelationSubsets f k
    have hpairs :
        (∑ S ∈ noRelationCardRange f Kmin Kmax,
            Bernoulli.weight Finset.univ p S) =
          ∑ x ∈ pairs, z * ∏ i ∈ x.2, Bernoulli.odds p i := by
      apply Finset.sum_bij
        (fun S (_ : S ∈ noRelationCardRange f Kmin Kmax) =>
          (⟨S.card, S⟩ : Σ _k : ℕ, Finset I))
      · intro S hS
        simp only [pairs, Finset.mem_sigma]
        have hs := hS
        simp only [noRelationCardRange, Finset.mem_filter, Finset.mem_univ,
          true_and] at hs
        exact ⟨Finset.mem_Icc.mpr ⟨hs.1, hs.2.1⟩, by
          simp [noRelationSubsets, hs.2.2]⟩
      · intro S₁ hS₁ S₂ hS₂ hEq
        exact congrArg Sigma.snd hEq
      · intro x hx
        have hxmem := Finset.mem_sigma.mp hx
        refine ⟨x.2, ?_, ?_⟩
        · have hxsub := hxmem.2
          simp only [noRelationSubsets, Finset.mem_filter, Finset.mem_univ,
            true_and] at hxsub
          simp only [noRelationCardRange, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨by simpa [hxsub.1] using (Finset.mem_Icc.mp hxmem.1).1,
            by simpa [hxsub.1] using (Finset.mem_Icc.mp hxmem.1).2, hxsub.2⟩
        · apply Sigma.ext
          · simpa [noRelationSubsets] using
              (Finset.mem_filter.mp hxmem.2).2.1
          · rfl
      · intro S hS
        exact Bernoulli.weight_eq_zeroBase_mul_prod_odds _ _ _
          (fun i _ => Finset.mem_univ i) (fun i _ => hp1 i)
    rw [hpairs]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    simpa [pairs] using (Finset.sum_sigma (s := Finset.Icc Kmin Kmax)
      (t := fun k => noRelationSubsets f k)
      (f := fun x : Σ _k : ℕ, Finset I =>
        z * ∏ i ∈ x.2, Bernoulli.odds p i))
  rw [heq]
  simpa [z, mul_assoc] using mul_le_mul_of_nonneg_left hraw hz0

noncomputable def relationSubsets
    {I : Type*} [Fintype I] (f : I → G) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S => ¬ noRelationSet f S

noncomputable def boundedRelationSubsets
    {I : Type*} [Fintype I] (f : I → G) (Kmax : ℕ) :
    Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S => ¬ noRelationSet f S ∧ S.card ≤ Kmax

/-- Complete finite upper-regime estimate: failure of a subset-product
relation is the union of two cardinality tails and the middle no-relation
event. -/
theorem one_sub_sum_weight_relation_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (p : I → ℝ) (f : I → G)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    {EW W ε rlo rhi : ℝ}
    (hEW : EW = ∑ i, p i)
    (hW : W = ∑ i, Bernoulli.odds p i)
    (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass (Bernoulli.odds p) f g / W -
        1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax)
    (hrlo0 : 0 < rlo) (hrlo1 : rlo < 1)
    (hKlo : (Kmin : ℝ) ≤ rlo * EW)
    (hrhi : 1 < rhi)
    (hKhi : rhi * EW ≤ (Kmax + 1 : ℕ)) :
    1 - (∑ S ∈ relationSubsets f,
        Bernoulli.weight Finset.univ p S) ≤
      Real.exp
          ((rlo * ((1 - rlo) / (2 * rlo)) +
            (1 / (1 + ((1 - rlo) / (2 * rlo))) - 1)) * EW) +
      Real.exp
          (((-(rhi * ((rhi - 1) / (2 * rhi)))) +
            (1 / (1 - ((rhi - 1) / (2 * rhi))) - 1)) * EW) +
      Bernoulli.zeroBase (Finset.univ : Finset I) p * Real.exp W *
        ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
          (Kmax : ℝ) * ε) := by
  classical
  let low : Finset (Finset I) :=
    Finset.univ.filter fun S => S.card < Kmin
  let high : Finset (Finset I) :=
    Finset.univ.filter fun S => Kmax + 1 ≤ S.card
  let middle := noRelationCardRange f Kmin Kmax
  have hweight0 (S : Finset I) :
      0 ≤ Bernoulli.weight Finset.univ p S :=
    Bernoulli.weight_nonneg _ _ (fun i _ => hp0 i)
      (fun i _ => (hp1 i).le) (by simp)
  have htotal :
      (∑ S : Finset I, Bernoulli.weight Finset.univ p S) = 1 := by
    simpa using Bernoulli.sum_weight_powerset
      (Finset.univ : Finset I) p
  have hcomplement :
      1 - (∑ S ∈ relationSubsets f,
          Bernoulli.weight Finset.univ p S) =
        ∑ S ∈ (Finset.univ : Finset (Finset I)).filter
          (noRelationSet f), Bernoulli.weight Finset.univ p S := by
    rw [← htotal]
    unfold relationSubsets
    simp only [Finset.sum_filter]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h : noRelationSet f S <;> simp [h]
  have hpartition :
      (∑ S ∈ (Finset.univ : Finset (Finset I)).filter
          (noRelationSet f), Bernoulli.weight Finset.univ p S) ≤
        (∑ S ∈ low, Bernoulli.weight Finset.univ p S) +
        (∑ S ∈ high, Bernoulli.weight Finset.univ p S) +
        ∑ S ∈ middle, Bernoulli.weight Finset.univ p S := by
    unfold low high middle noRelationCardRange
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S _
    by_cases hn : noRelationSet f S
    · simp only [hn, if_true]
      split_ifs <;> simp_all <;> omega
    · simp only [hn, if_false, and_false]
      split_ifs <;> simp_all [hweight0 S]
  have hlow :
      (∑ S ∈ low, Bernoulli.weight Finset.univ p S) ≤
        Real.exp
          ((rlo * ((1 - rlo) / (2 * rlo)) +
            (1 / (1 + ((1 - rlo) / (2 * rlo))) - 1)) * EW) := by
    simpa [low] using Bernoulli.lower_tail_chernoff
      (Finset.univ : Finset I) p (fun i _ => hp0 i)
      (fun i _ => (hp1 i).le) hEW hrlo0 hrlo1 hKlo
  have hhigh :
      (∑ S ∈ high, Bernoulli.weight Finset.univ p S) ≤
        Real.exp
          (((-(rhi * ((rhi - 1) / (2 * rhi)))) +
            (1 / (1 - ((rhi - 1) / (2 * rhi))) - 1)) * EW) := by
    simpa [high] using Bernoulli.upper_tail_chernoff
      (Finset.univ : Finset I) p (fun i _ => hp0 i)
      (fun i _ => (hp1 i).le) hEW hrhi hKhi
  have hmiddle := sum_weight_noRelation_card_range_le p f hp0 hp1
    hW hWpos hε hTV hKmin hKK
  rw [hcomplement]
  exact hpartition.trans (add_le_add (add_le_add hlow hhigh) hmiddle)

/-- Safe version in which the whole selected set has cardinality at most
`Kmax`; consequently every witnessing relation has at most `Kmax` factors. -/
theorem one_sub_sum_weight_boundedRelation_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (p : I → ℝ) (f : I → G)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    {EW W ε rlo rhi : ℝ}
    (hEW : EW = ∑ i, p i)
    (hW : W = ∑ i, Bernoulli.odds p i)
    (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass (Bernoulli.odds p) f g / W -
        1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax)
    (hrlo0 : 0 < rlo) (hrlo1 : rlo < 1)
    (hKlo : (Kmin : ℝ) ≤ rlo * EW)
    (hrhi : 1 < rhi)
    (hKhi : rhi * EW ≤ (Kmax + 1 : ℕ)) :
    1 - (∑ S ∈ boundedRelationSubsets f Kmax,
        Bernoulli.weight Finset.univ p S) ≤
      Real.exp
          ((rlo * ((1 - rlo) / (2 * rlo)) +
            (1 / (1 + ((1 - rlo) / (2 * rlo))) - 1)) * EW) +
      2 * Real.exp
          (((-(rhi * ((rhi - 1) / (2 * rhi)))) +
            (1 / (1 - ((rhi - 1) / (2 * rhi))) - 1)) * EW) +
      Bernoulli.zeroBase (Finset.univ : Finset I) p * Real.exp W *
        ((Fintype.card G : ℝ) / ((2 : ℝ) ^ Kmin - 1) +
          (Kmax : ℝ) * ε) := by
  classical
  let high : Finset (Finset I) :=
    Finset.univ.filter fun S => Kmax + 1 ≤ S.card
  have hweight0 (S : Finset I) :
      0 ≤ Bernoulli.weight Finset.univ p S :=
    Bernoulli.weight_nonneg _ _ (fun i _ => hp0 i)
      (fun i _ => (hp1 i).le) (by simp)
  have hrel := one_sub_sum_weight_relation_le p f hp0 hp1 hEW hW
    hWpos hε hTV hKmin hKK hrlo0 hrlo1 hKlo hrhi hKhi
  have hhigh :
      (∑ S ∈ high, Bernoulli.weight Finset.univ p S) ≤
        Real.exp
          (((-(rhi * ((rhi - 1) / (2 * rhi)))) +
            (1 / (1 - ((rhi - 1) / (2 * rhi))) - 1)) * EW) := by
    simpa [high] using Bernoulli.upper_tail_chernoff
      (Finset.univ : Finset I) p (fun i _ => hp0 i)
      (fun i _ => (hp1 i).le) hEW hrhi hKhi
  have hdiff :
      (∑ S ∈ relationSubsets f,
          Bernoulli.weight Finset.univ p S) -
        (∑ S ∈ boundedRelationSubsets f Kmax,
          Bernoulli.weight Finset.univ p S) ≤
        ∑ S ∈ high, Bernoulli.weight Finset.univ p S := by
    unfold relationSubsets boundedRelationSubsets high
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro S _
    by_cases hr : noRelationSet f S
    · simp only [hr, not_true_eq_false, if_false, zero_sub]
      split_ifs <;> simp_all [hweight0 S]
    · by_cases hk : S.card ≤ Kmax
      · simp only [hr, not_false_eq_true, hk, if_true, sub_self]
        split_ifs <;> simp_all [hweight0 S]
      · have : Kmax + 1 ≤ S.card := by omega
        simp [hr, hk, this]
  have hcombine :
      1 - (∑ S ∈ boundedRelationSubsets f Kmax,
        Bernoulli.weight Finset.univ p S) ≤
      (1 - ∑ S ∈ relationSubsets f,
        Bernoulli.weight Finset.univ p S) +
      ∑ S ∈ high, Bernoulli.weight Finset.univ p S := by
    linarith
  calc
    1 - (∑ S ∈ boundedRelationSubsets f Kmax,
        Bernoulli.weight Finset.univ p S) ≤
        (1 - ∑ S ∈ relationSubsets f,
          Bernoulli.weight Finset.univ p S) +
        ∑ S ∈ high, Bernoulli.weight Finset.univ p S := hcombine
    _ ≤ _ := by linarith

/-! The dual estimate used for the zero-limit direction.  Here a selected
subset is bad when one of its nonempty subproducts lands in a prescribed
finite target set. -/

def hitsSet {I : Type*} (f : I → G) (B : Finset G) (S : Finset I) : Prop :=
  ∃ T : Finset I, T ⊆ S ∧ T.Nonempty ∧ (∏ i ∈ T, f i) ∈ B

noncomputable def hittingSubsets {I : Type*} [Fintype I]
    (f : I → G) (B : Finset G) (K : ℕ) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter fun S => S.card = K ∧ hitsSet f B S

theorem factorial_mul_hitsSet_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℝ) (f : I → G) (B : Finset G) (hw : ∀ i, 0 ≤ w i)
    {W ε : ℝ} (hW : W = ∑ i, w i) (hWpos : 0 < W)
    (hTV : (∑ g : G,
      |residueMass w f g / W - 1 / (Fintype.card G : ℝ)|) ≤ ε)
    {K : ℕ} (hK : 1 ≤ K) :
    (K.factorial : ℝ) *
        (∑ S ∈ hittingSubsets f B K, ∏ i ∈ S, w i) ≤
      W ^ K *
        ((B.card : ℝ) * ((2 : ℝ) ^ K - 1) /
            (Fintype.card G : ℝ) + (K : ℝ) * ε) := by
  classical
  let Ptuple : (Fin K → I) → Prop :=
    fun v => hitsTuple B (fun j => f (v j))
  have hlift :
      (K.factorial : ℝ) *
          (∑ S ∈ hittingSubsets f B K, ∏ i ∈ S, w i) ≤
        ∑ v ∈ (Finset.univ : Finset (Fin K → I)).filter Ptuple,
          ∏ j, w (v j) := by
    have hraw := factorial_mul_sum_subsets_le_sum_tuples w hw
      (hitsSet f B) Ptuple (by
        intro S hS σ
        obtain ⟨T, hTS, hTne, hTB⟩ := hS
        let e : Fin K → I := enumeration (S, σ)
        have heinj : Function.Injective e := by
          intro i j hij
          apply σ.injective
          exact (S.1.orderEmbOfFin S.2).injective hij
        have herange : Finset.image e Finset.univ = S.1 := by
          calc
            Finset.image e Finset.univ =
                Finset.image (S.1.orderEmbOfFin S.2)
                  (Finset.image σ Finset.univ) := by
              rw [← Finset.image_comp]
              rfl
            _ = Finset.image (S.1.orderEmbOfFin S.2) Finset.univ := by
              congr 1
              ext j
              simp
            _ = S.1 := Finset.image_orderEmbOfFin_univ _ _
        let A : Finset (Fin K) := Finset.univ.filter fun j => e j ∈ T
        have hAne : A.Nonempty := by
          obtain ⟨i, hiT⟩ := hTne
          have hiS := hTS hiT
          rw [← herange] at hiS
          obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hiS
          exact ⟨j, by simp [A, hji, hiT]⟩
        refine ⟨A, hAne, ?_⟩
        have himage : Finset.image e A = T := by
          ext i
          constructor
          · intro hi
            obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hi
            have hej : e j ∈ T := by simpa [A] using hj
            simpa [hji] using hej
          · intro hi
            have hiS := hTS hi
            rw [← herange] at hiS
            obtain ⟨j, _, hji⟩ := Finset.mem_image.mp hiS
            apply Finset.mem_image.mpr
            refine ⟨j, ?_, hji⟩
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
            simpa [hji] using hi
        have hprodEq : Erdos696.subsetProd A (fun j => f (e j)) =
            ∏ i ∈ T, f i := by
          unfold Erdos696.subsetProd
          rw [← Finset.prod_image heinj.injOn, himage]
        rw [hprodEq]
        exact hTB)
    simpa [hittingSubsets] using hraw
  have htuple := sum_tuple_event_le_of_residue_l1 w f hw hW hWpos hTV
    (P := hitsTuple B)
    (B := (B.card : ℝ) * ((2 : ℝ) ^ K - 1) /
      (Fintype.card G : ℝ))
    (uniform_hitsTuple_le (G := G) hK B)
  exact hlift.trans (by simpa [Ptuple] using htuple)

/-- Summed weighted target-hitting bound over a cardinality window. -/
theorem sum_hitting_odds_card_range_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (w : I → ℝ) (f : I → G) (B : Finset G) (hw : ∀ i, 0 ≤ w i)
    {W ε : ℝ} (hW : W = ∑ i, w i) (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass w f g / W - 1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax) :
    (∑ k ∈ Finset.Icc Kmin Kmax,
        ∑ S ∈ hittingSubsets f B k, ∏ i ∈ S, w i) ≤
      Real.exp W *
        ((B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
            (Fintype.card G : ℝ) + (Kmax : ℝ) * ε) := by
  have hNpos : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast Fintype.card_pos (α := G)
  have hBnonneg : 0 ≤
      (B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
          (Fintype.card G : ℝ) + (Kmax : ℝ) * ε := by
    have hpow : (1 : ℝ) ≤ 2 ^ Kmax := one_le_pow₀ (by norm_num)
    positivity
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc Kmin Kmax) :
      (∑ S ∈ hittingSubsets f B k, ∏ i ∈ S, w i) ≤
        (W ^ k / (k.factorial : ℝ)) *
          ((B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
              (Fintype.card G : ℝ) + (Kmax : ℝ) * ε) := by
    have hkmin : Kmin ≤ k := (Finset.mem_Icc.mp hk).1
    have hkmax : k ≤ Kmax := (Finset.mem_Icc.mp hk).2
    have hfixed := factorial_mul_hitsSet_le w f B hw hW hWpos hTV
      (hKmin.trans hkmin)
    have hpowmono : (2 : ℝ) ^ k ≤ 2 ^ Kmax :=
      pow_le_pow_right₀ one_le_two hkmax
    have hsmall :
        (B.card : ℝ) * ((2 : ℝ) ^ k - 1) /
              (Fintype.card G : ℝ) + (k : ℝ) * ε ≤
          (B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
              (Fintype.card G : ℝ) + (Kmax : ℝ) * ε := by
      apply add_le_add
      · gcongr
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkmax) hε
    have hfacpos : (0 : ℝ) < k.factorial := by positivity
    calc
      (∑ S ∈ hittingSubsets f B k, ∏ i ∈ S, w i) ≤
          W ^ k / (k.factorial : ℝ) *
            ((B.card : ℝ) * ((2 : ℝ) ^ k - 1) /
                (Fintype.card G : ℝ) + (k : ℝ) * ε) := by
        rw [show W ^ k / (k.factorial : ℝ) * _ =
            (W ^ k * ((B.card : ℝ) * ((2 : ℝ) ^ k - 1) /
              (Fintype.card G : ℝ) + (k : ℝ) * ε)) /
                (k.factorial : ℝ) by ring]
        exact (le_div_iff₀ hfacpos).2 (by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hfixed)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  calc
    (∑ k ∈ Finset.Icc Kmin Kmax,
        ∑ S ∈ hittingSubsets f B k, ∏ i ∈ S, w i) ≤
      ∑ k ∈ Finset.Icc Kmin Kmax,
        (W ^ k / (k.factorial : ℝ)) *
          ((B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
              (Fintype.card G : ℝ) + (Kmax : ℝ) * ε) :=
        Finset.sum_le_sum hterm
    _ = (∑ k ∈ Finset.Icc Kmin Kmax,
          W ^ k / (k.factorial : ℝ)) *
          ((B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
              (Fintype.card G : ℝ) + (Kmax : ℝ) * ε) := by
      rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sum_pow_div_factorial_le_exp W hWpos.le _) hBnonneg

/-- Cardinality-window target-hitting event under the Bernoulli law. -/
noncomputable def hittingCardRange
    {I : Type*} [Fintype I] (f : I → G) (B : Finset G)
    (Kmin Kmax : ℕ) : Finset (Finset I) := by
  classical
  exact Finset.univ.filter
    (fun S => Kmin ≤ S.card ∧ S.card ≤ Kmax ∧ hitsSet f B S)

/-- Bernoulli form of the target-hitting estimate.  The exact
`zeroBase * exp W` normalization is retained for the sharp exponent. -/
theorem sum_weight_hitting_card_range_le
    {I : Type*} [Fintype I] [LinearOrder I]
    (p : I → ℝ) (f : I → G) (B : Finset G)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1)
    {W ε : ℝ} (hW : W = ∑ i, Bernoulli.odds p i)
    (hWpos : 0 < W) (hε : 0 ≤ ε)
    (hTV : (∑ g : G,
      |residueMass (Bernoulli.odds p) f g / W -
        1 / (Fintype.card G : ℝ)|) ≤ ε)
    {Kmin Kmax : ℕ} (hKmin : 1 ≤ Kmin) (hKK : Kmin ≤ Kmax) :
    (∑ S ∈ hittingCardRange f B Kmin Kmax,
          Bernoulli.weight Finset.univ p S) ≤
      Bernoulli.zeroBase (Finset.univ : Finset I) p * Real.exp W *
        ((B.card : ℝ) * ((2 : ℝ) ^ Kmax - 1) /
            (Fintype.card G : ℝ) + (Kmax : ℝ) * ε) := by
  classical
  let z := Bernoulli.zeroBase (Finset.univ : Finset I) p
  have hw0 (i : I) : 0 ≤ Bernoulli.odds p i := by
    unfold Bernoulli.odds
    exact div_nonneg (hp0 i) (sub_nonneg.mpr (hp1 i).le)
  have hz0 : 0 ≤ z := Bernoulli.zeroBase_nonneg _ _
    (fun i _ => (hp1 i).le)
  have hraw := sum_hitting_odds_card_range_le
    (Bernoulli.odds p) f B hw0 hW hWpos hε hTV hKmin hKK
  have heq :
      (∑ S ∈ hittingCardRange f B Kmin Kmax,
            Bernoulli.weight Finset.univ p S) =
        z * ∑ k ∈ Finset.Icc Kmin Kmax,
          ∑ S ∈ hittingSubsets f B k,
            ∏ i ∈ S, Bernoulli.odds p i := by
    let pairs : Finset (Σ _k : ℕ, Finset I) :=
      (Finset.Icc Kmin Kmax).sigma fun k => hittingSubsets f B k
    have hpairs :
        (∑ S ∈ hittingCardRange f B Kmin Kmax,
            Bernoulli.weight Finset.univ p S) =
          ∑ x ∈ pairs, z * ∏ i ∈ x.2, Bernoulli.odds p i := by
      apply Finset.sum_bij
        (fun S (_ : S ∈ hittingCardRange f B Kmin Kmax) =>
          (⟨S.card, S⟩ : Σ _k : ℕ, Finset I))
      · intro S hS
        simp only [pairs, Finset.mem_sigma]
        have hs := hS
        simp only [hittingCardRange, Finset.mem_filter, Finset.mem_univ,
          true_and] at hs
        exact ⟨Finset.mem_Icc.mpr ⟨hs.1, hs.2.1⟩, by
          simp [hittingSubsets, hs.2.2]⟩
      · intro S₁ hS₁ S₂ hS₂ hEq
        exact congrArg Sigma.snd hEq
      · intro x hx
        have hxmem := Finset.mem_sigma.mp hx
        refine ⟨x.2, ?_, ?_⟩
        · have hxsub := hxmem.2
          simp only [hittingSubsets, Finset.mem_filter, Finset.mem_univ,
            true_and] at hxsub
          simp only [hittingCardRange, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact ⟨by simpa [hxsub.1] using (Finset.mem_Icc.mp hxmem.1).1,
            by simpa [hxsub.1] using (Finset.mem_Icc.mp hxmem.1).2, hxsub.2⟩
        · apply Sigma.ext
          · simpa [hittingSubsets] using
              (Finset.mem_filter.mp hxmem.2).2.1
          · rfl
      · intro S hS
        exact Bernoulli.weight_eq_zeroBase_mul_prod_odds _ _ _
          (fun i _ => Finset.mem_univ i) (fun i _ => hp1 i)
    rw [hpairs]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    simpa [pairs] using (Finset.sum_sigma (s := Finset.Icc Kmin Kmax)
      (t := fun k => hittingSubsets f B k)
      (f := fun x : Σ _k : ℕ, Finset I =>
        z * ∏ i ∈ x.2, Bernoulli.odds p i))
  rw [heq]
  simpa [z, mul_assoc] using mul_le_mul_of_nonneg_left hraw hz0

end SubsetProductEvents

end

end Erdos697.WeightedSubset
