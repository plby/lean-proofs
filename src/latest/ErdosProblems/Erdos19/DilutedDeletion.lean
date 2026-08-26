import ErdosProblems.Erdos19.Core

/-! # Deletion certificates for a sparsely activated coloring round

Each vertex is active with probability `1 / A`. A deletion witness requires
three prescribed active color values, retaining all three activation factors.
-/

namespace Erdos19

attribute [local instance] Classical.propDecidable

theorem card_fun_prescribed_triples {V I K : Type*}
    [Fintype V] [Fintype I] [Fintype K]
    (first second third : I → V)
    (hinj : Function.Injective (Sum.elim first (Sum.elim second third) : I ⊕ (I ⊕ I) → V))
    (value : I → K) :
    Nat.card {f : V → K // ∀ i, f (first i) = value i ∧
      f (second i) = value i ∧ f (third i) = value i} =
      Fintype.card K ^ (Fintype.card V - 3 * Fintype.card I) := by
  let e : I ⊕ (I ⊕ I) → V := Sum.elim first (Sum.elim second third)
  let g : I ⊕ (I ⊕ I) → K := Sum.elim value (Sum.elim value value)
  let equiv : {f : V → K // ∀ i, f (first i) = value i ∧
      f (second i) = value i ∧ f (third i) = value i} ≃
      {f : V → K // ∀ i, f (e i) = g i} :=
    { toFun := fun f ↦ ⟨f.1, fun i ↦ by
        rcases i with i | i | i
        · exact (f.2 i).1
        · exact (f.2 i).2.1
        · exact (f.2 i).2.2⟩
      invFun := fun f ↦ ⟨f.1, fun i ↦
        ⟨f.2 (.inl i), f.2 (.inr (.inl i)), f.2 (.inr (.inr i))⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Nat.card_congr equiv, card_fun_comp_eq_of_injective e hinj g]
  congr 2
  simp only [Fintype.card_sum]
  omega

def dilutedDeletedCollisionColors {V : Type*} (G : _root_.SimpleGraph V) {A C : ℕ}
    (active : Fin A) (sample : V → Fin A × Fin C) (v : V) : Set (Fin C) :=
  {a | ∃ p q z : V, p ≠ q ∧ ¬G.Adj p q ∧ G.Adj v p ∧ G.Adj v q ∧
    sample p = (active, a) ∧ sample q = (active, a) ∧ G.Adj p z ∧ sample z = (active, a)}

def dilutedDeletionCertificateEvent {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C s : ℕ} (active : Fin A)
    (v : V) (d : MRDeletionCertificateIndex G v C s) : Set (V → Fin A × Fin C) :=
  {sample | ∀ a : d.1.1, sample (d.2 a).1.1.1 = (active, a.1) ∧
    sample (d.2 a).1.1.2 = (active, a.1) ∧ sample (d.2 a).1.2 = (active, a.1)}

theorem card_dilutedDeletionCertificateEvent_le {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C s : ℕ} (active : Fin A)
    (v : V) (d : MRDeletionCertificateIndex G v C s) :
    (eventFinset (dilutedDeletionCertificateEvent G active v d)).card ≤
      (A * C) ^ (Fintype.card V - 3 * s) := by
  classical
  by_cases hne : (dilutedDeletionCertificateEvent G active v d).Nonempty
  · obtain ⟨sample, hsample⟩ := hne
    have hsecond : (fun x ↦ (sample x).2) ∈ mrDeletionCertificateEvent G v d := by
      intro a
      exact ⟨congrArg Prod.snd (hsample a).1, congrArg Prod.snd (hsample a).2.1,
        congrArg Prod.snd (hsample a).2.2⟩
    have hinj := mrDeletionCertificate_endpoint_injective_of_mem G v d _ hsecond
    have hcount := card_fun_prescribed_triples
      (fun a : d.1.1 ↦ (d.2 a).1.1.1) (fun a : d.1.1 ↦ (d.2 a).1.1.2)
      (fun a : d.1.1 ↦ (d.2 a).1.2) hinj (fun a : d.1.1 ↦ (active, a.1))
    rw [card_eventFinset_eq_ncard, ← Set.fintypeCard_eq_ncard]
    rw [← Nat.card_eq_fintype_card (α := ↥(dilutedDeletionCertificateEvent G active v d))]
    change Nat.card {sample : V → Fin A × Fin C // ∀ a : d.1.1,
      sample (d.2 a).1.1.1 = (active, a.1) ∧ sample (d.2 a).1.1.2 = (active, a.1) ∧
        sample (d.2 a).1.2 = (active, a.1)} ≤ _
    rw [hcount, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_coe, d.1.2]
  · have hempty := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp [eventFinset]

theorem dilutedDeletionHighEvent_subset_certificateUnion {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V) (s : ℕ) :
    eventFinset {sample : V → Fin A × Fin C |
      s ≤ (dilutedDeletedCollisionColors G active sample v).ncard} ⊆
      Finset.univ.biUnion (fun d : MRDeletionCertificateIndex G v C s ↦
        eventFinset (dilutedDeletionCertificateEvent G active v d)) := by
  classical
  intro sample hsample
  rw [mem_eventFinset] at hsample
  let D := dilutedDeletedCollisionColors G active sample v
  have hcard : s ≤ (eventFinset D).card := by
    rw [card_eventFinset_eq_ncard]
    exact hsample
  obtain ⟨S, hSD, hScard⟩ := Finset.exists_subset_card_eq hcard
  let S' : {S : Finset (Fin C) // S.card = s} := ⟨S, hScard⟩
  have hdata (a : S'.1) : ∃ p q z : V,
      p ≠ q ∧ ¬G.Adj p q ∧ G.Adj v p ∧ G.Adj v q ∧
      sample p = (active, a.1) ∧ sample q = (active, a.1) ∧
      G.Adj p z ∧ sample z = (active, a.1) :=
    (mem_eventFinset D a.1).mp (hSD a.2)
  choose p q z hspec using hdata
  let witness (a : S'.1) : {t // t ∈ mrDeletionWitnessTriples G v} :=
    ⟨((p a, q a), z a), (mem_mrDeletionWitnessTriples G v _).mpr
      ⟨(hspec a).1, (hspec a).2.1, (hspec a).2.2.1,
        (hspec a).2.2.2.1, (hspec a).2.2.2.2.2.2.1⟩⟩
  let d : MRDeletionCertificateIndex G v C s := ⟨S', witness⟩
  have hcert : sample ∈ dilutedDeletionCertificateEvent G active v d := by
    intro a
    exact ⟨(hspec a).2.2.2.2.1, (hspec a).2.2.2.2.2.1, (hspec a).2.2.2.2.2.2.2⟩
  exact Finset.mem_biUnion.mpr ⟨d, Finset.mem_univ _, (mem_eventFinset _ sample).mpr hcert⟩

theorem card_dilutedDeletionHighEvent_le {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) {A C : ℕ} (active : Fin A) (v : V) (s : ℕ) :
    (eventFinset {sample : V → Fin A × Fin C |
      s ≤ (dilutedDeletedCollisionColors G active sample v).ncard}).card ≤
      (C.choose s * (mrDeletionWitnessTriples G v).card ^ s) *
        (A * C) ^ (Fintype.card V - 3 * s) := by
  classical
  calc
    _ ≤ (Finset.univ.biUnion (fun d : MRDeletionCertificateIndex G v C s ↦
        eventFinset (dilutedDeletionCertificateEvent G active v d))).card :=
      Finset.card_le_card (dilutedDeletionHighEvent_subset_certificateUnion G active v s)
    _ ≤ ∑ d : MRDeletionCertificateIndex G v C s,
        (eventFinset (dilutedDeletionCertificateEvent G active v d)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d : MRDeletionCertificateIndex G v C s,
        (A * C) ^ (Fintype.card V - 3 * s) :=
      Finset.sum_le_sum (fun d _ ↦ card_dilutedDeletionCertificateEvent_le G active v d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      card_MRDeletionCertificateIndex]

#print axioms card_dilutedDeletionHighEvent_le

end Erdos19
