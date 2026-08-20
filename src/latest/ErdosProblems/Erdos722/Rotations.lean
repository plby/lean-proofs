/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.IntegralGenerators
import ErdosProblems.Erdos722.Prune
import ErdosProblems.Erdos722.Probability
import ErdosProblems.Erdos722.RootedEmbedding
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Random vertex rotations for Erdős 722

This file develops the finite permutation action used in Lemma 6.3 of the
short proof.  Probabilities are represented by cardinalities of explicit
finite sample spaces; no measure-theoretic quotient is needed.
-/

namespace Erdos722.Rotations

open Finset

noncomputable section

/-- Relabel a vertex set by a permutation. -/
def rotateEdge (σ : Equiv.Perm (Fin n)) (e : Finset (Fin n)) :
    Finset (Fin n) :=
  σ.finsetCongr e

/-- Relabel a finite edge or block family by a permutation. -/
def rotateFamily (σ : Equiv.Perm (Fin n))
    (K : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  σ.finsetCongr.finsetCongr K

@[simp] lemma rotateEdge_card (σ : Equiv.Perm (Fin n))
    (e : Finset (Fin n)) :
    (rotateEdge σ e).card = e.card := by
  simp [rotateEdge]

@[simp] lemma rotateFamily_card (σ : Equiv.Perm (Fin n))
    (K : Finset (Finset (Fin n))) :
    (rotateFamily σ K).card = K.card := by
  simp [rotateFamily]

@[simp] lemma mem_rotateFamily
    {σ : Equiv.Perm (Fin n)} {K : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} :
    e ∈ rotateFamily σ K ↔ rotateEdge σ.symm e ∈ K := by
  simp [rotateFamily, rotateEdge]

lemma rotateEdge_subset_rotateEdge
    (σ : Equiv.Perm (Fin n)) {e f : Finset (Fin n)} (hef : e ⊆ f) :
    rotateEdge σ e ⊆ rotateEdge σ f := by
  intro x hx
  change x ∈ e.map σ.toEmbedding at hx
  change x ∈ f.map σ.toEmbedding
  exact Finset.mem_map_equiv.mpr
    (hef (Finset.mem_map_equiv.mp hx))

@[simp] lemma rotateEdge_trans
    (σ τ : Equiv.Perm (Fin n)) (e : Finset (Fin n)) :
    rotateEdge (σ.trans τ) e = rotateEdge τ (rotateEdge σ e) := by
  change (σ.trans τ).finsetCongr e =
    τ.finsetCongr (σ.finsetCongr e)
  exact (Equiv.congr_fun (Equiv.finsetCongr_trans σ τ) e).symm

@[simp] lemma rotateEdge_symm_rotateEdge
    (σ : Equiv.Perm (Fin n)) (e : Finset (Fin n)) :
    rotateEdge σ.symm (rotateEdge σ e) = e := by
  change σ.symm.finsetCongr (σ.finsetCongr e) = e
  exact σ.finsetCongr.left_inv e

@[simp] lemma rotateEdge_rotateEdge_symm
    (σ : Equiv.Perm (Fin n)) (e : Finset (Fin n)) :
    rotateEdge σ (rotateEdge σ.symm e) = e := by
  simpa using rotateEdge_symm_rotateEdge σ.symm e

@[simp] lemma rotateFamily_trans
    (σ τ : Equiv.Perm (Fin n)) (K : Finset (Finset (Fin n))) :
    rotateFamily (σ.trans τ) K = rotateFamily τ (rotateFamily σ K) := by
  ext e
  simp [mem_rotateFamily, rotateEdge_trans]

@[simp] lemma rotateFamily_symm_rotateFamily
    (σ : Equiv.Perm (Fin n)) (K : Finset (Finset (Fin n))) :
    rotateFamily σ.symm (rotateFamily σ K) = K := by
  change σ.symm.finsetCongr.finsetCongr
      (σ.finsetCongr.finsetCongr K) = K
  exact σ.finsetCongr.finsetCongr.left_inv K

@[simp] lemma rotateFamily_rotateFamily_symm
    (σ : Equiv.Perm (Fin n)) (K : Finset (Finset (Fin n))) :
    rotateFamily σ (rotateFamily σ.symm K) = K := by
  simpa using rotateFamily_symm_rotateFamily σ.symm K

lemma rotateFamily_mono (σ : Equiv.Perm (Fin n))
    {A B : Finset (Finset (Fin n))} (hAB : A ⊆ B) :
    rotateFamily σ A ⊆ rotateFamily σ B := by
  intro e he
  apply mem_rotateFamily.mpr
  exact hAB (mem_rotateFamily.mp he)

@[simp] lemma rotateFamily_sdiff
    (σ : Equiv.Perm (Fin n))
    (A B : Finset (Finset (Fin n))) :
    rotateFamily σ (A \ B) = rotateFamily σ A \ rotateFamily σ B := by
  ext e
  simp [mem_rotateFamily]

@[simp] lemma rotateFamily_union
    (σ : Equiv.Perm (Fin n))
    (A B : Finset (Finset (Fin n))) :
    rotateFamily σ (A ∪ B) = rotateFamily σ A ∪ rotateFamily σ B := by
  ext e
  simp [mem_rotateFamily]

lemma rotateEdge_subset_iff
    (σ : Equiv.Perm (Fin n)) {e f : Finset (Fin n)} :
    rotateEdge σ e ⊆ rotateEdge σ f ↔ e ⊆ f := by
  constructor
  · intro h
    have := rotateEdge_subset_rotateEdge σ.symm h
    simpa using this
  · exact rotateEdge_subset_rotateEdge σ

lemma subset_rotateEdge_iff
    (σ : Equiv.Perm (Fin n)) {e f : Finset (Fin n)} :
    e ⊆ rotateEdge σ f ↔ rotateEdge σ.symm e ⊆ f := by
  constructor
  · intro h
    have := rotateEdge_subset_rotateEdge σ.symm h
    simpa using this
  · intro h
    have := rotateEdge_subset_rotateEdge σ h
    simpa using this

lemma rotateEdge_powersetCard
    (σ : Equiv.Perm (Fin n)) (Q : Finset (Fin n)) (r : ℕ) :
    (rotateEdge σ Q).powersetCard r =
      rotateFamily σ (Q.powersetCard r) := by
  ext e
  rw [mem_rotateFamily]
  simp only [Finset.mem_powersetCard, rotateEdge_card]
  exact and_congr (subset_rotateEdge_iff σ) Iff.rfl

lemma rotateFamily_cliquesIn
    (σ : Equiv.Perm (Fin n)) (K : Finset (Finset (Fin n)))
    (q r : ℕ) :
    rotateFamily σ (Erdos722.IntegralGenerators.cliquesIn n q r K) =
      Erdos722.IntegralGenerators.cliquesIn n q r (rotateFamily σ K) := by
  ext Q
  rw [mem_rotateFamily]
  simp only [Erdos722.IntegralGenerators.mem_cliquesIn, rotateEdge_card]
  constructor
  · rintro ⟨hcard, hsub⟩
    refine ⟨hcard, ?_⟩
    rw [show Q = rotateEdge σ (rotateEdge σ.symm Q) by simp,
      rotateEdge_powersetCard]
    exact rotateFamily_mono σ hsub
  · rintro ⟨hcard, hsub⟩
    refine ⟨hcard, ?_⟩
    have hrot := rotateFamily_mono σ.symm hsub
    simpa [rotateEdge_powersetCard] using hrot

lemma counterLoad_rotateFamily
    (σ : Equiv.Perm (Fin n)) (selected : Finset (Finset (Fin n)))
    (f : Finset (Fin n)) :
    Erdos722.Generators.counterLoad
        (fun a Q : Finset (Fin n) ↦ a ⊆ Q)
        (rotateFamily σ selected) (rotateEdge σ f) =
      Erdos722.Generators.counterLoad
        (fun a Q : Finset (Fin n) ↦ a ⊆ Q) selected f := by
  classical
  unfold Erdos722.Generators.counterLoad
  let left := (rotateFamily σ selected).filter
    (fun Q ↦ rotateEdge σ f ⊆ Q)
  let right := selected.filter (fun Q ↦ f ⊆ Q)
  have heq : left = rotateFamily σ right := by
    ext Q
    simp only [left, right, Finset.mem_filter, mem_rotateFamily]
    rw [show rotateEdge σ f ⊆ Q ↔
        f ⊆ rotateEdge σ.symm Q by
      simpa using (rotateEdge_subset_iff σ
        (e := f) (f := rotateEdge σ.symm Q))]
  rw [show (rotateFamily σ selected).filter
      (fun Q ↦ rotateEdge σ f ⊆ Q) = left by rfl,
    heq, rotateFamily_card]

lemma rotateFamily_twoCapSaturatedCliques
    (σ : Equiv.Perm (Fin n)) (K selected : Finset (Finset (Fin n)))
    (q r faceCap edgeCap : ℕ) :
    rotateFamily σ
        (Erdos722.IntegralGenerators.twoCapSaturatedCliques
          n q r faceCap edgeCap K selected) =
      Erdos722.IntegralGenerators.twoCapSaturatedCliques
        n q r faceCap edgeCap
          (rotateFamily σ K) (rotateFamily σ selected) := by
  classical
  ext Q
  rw [mem_rotateFamily]
  simp only [Erdos722.IntegralGenerators.mem_twoCapSaturatedCliques,
    ← rotateFamily_cliquesIn]
  rw [mem_rotateFamily]
  constructor
  · rintro ⟨hQ, hface | hedge⟩
    · refine ⟨hQ, Or.inl ?_⟩
      obtain ⟨f, hfcard, hfQ, hfload⟩ := hface
      refine ⟨rotateEdge σ f, by simpa, ?_, ?_⟩
      · have := rotateEdge_subset_rotateEdge σ hfQ
        simpa using this
      · simpa [counterLoad_rotateFamily] using hfload
    · refine ⟨hQ, Or.inr ?_⟩
      obtain ⟨e, hecard, heQ, heload⟩ := hedge
      refine ⟨rotateEdge σ e, by simpa, ?_, ?_⟩
      · have := rotateEdge_subset_rotateEdge σ heQ
        simpa using this
      · simpa [counterLoad_rotateFamily] using heload
  · rintro ⟨hQ, hface | hedge⟩
    · refine ⟨hQ, Or.inl ?_⟩
      obtain ⟨f, hfcard, hfQ, hfload⟩ := hface
      refine ⟨rotateEdge σ.symm f, by simpa, ?_, ?_⟩
      · have := rotateEdge_subset_rotateEdge σ.symm hfQ
        simpa using this
      · have h := counterLoad_rotateFamily σ.symm
          (rotateFamily σ selected) f
        rw [rotateFamily_symm_rotateFamily] at h
        rw [h]
        exact hfload
    · refine ⟨hQ, Or.inr ?_⟩
      obtain ⟨e, hecard, heQ, heload⟩ := hedge
      refine ⟨rotateEdge σ.symm e, by simpa, ?_, ?_⟩
      · have := rotateEdge_subset_rotateEdge σ.symm heQ
        simpa using this
      · have h := counterLoad_rotateFamily σ.symm
          (rotateFamily σ selected) e
        rw [rotateFamily_symm_rotateFamily] at h
        rw [h]
        exact heload

lemma rotateFamily_twoCapUnsaturatedCliques
    (σ : Equiv.Perm (Fin n)) (K selected : Finset (Finset (Fin n)))
    (q r faceCap edgeCap : ℕ) :
    rotateFamily σ
        (Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
          n q r faceCap edgeCap K selected) =
      Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
        n q r faceCap edgeCap
          (rotateFamily σ K) (rotateFamily σ selected) := by
  simp [Erdos722.IntegralGenerators.twoCapUnsaturatedCliques,
    rotateFamily_cliquesIn, rotateFamily_twoCapSaturatedCliques]

/-- Reindex a restricted modular edge vector along a vertex permutation. -/
def restrictedRotateAddEquiv (N : ℕ) (σ : Equiv.Perm (Fin n))
    (K : Finset (Finset (Fin n))) :
    (↑K → ZMod N) ≃+ (↑(rotateFamily σ K) → ZMod N) where
  toFun x e := x ⟨rotateEdge σ.symm e.1, mem_rotateFamily.mp e.2⟩
  invFun y e := y ⟨rotateEdge σ e.1, by
    apply mem_rotateFamily.mpr
    simpa using e.2⟩
  left_inv x := by
    funext e
    simp
  right_inv y := by
    funext e
    simp
  map_add' x y := by
    funext e
    rfl

lemma restrictedRotateAddEquiv_modCliqueBoundaryOn
    (N r : ℕ) (σ : Equiv.Perm (Fin n))
    (K : Finset (Finset (Fin n))) (Q : Finset (Fin n)) :
    restrictedRotateAddEquiv N σ K
        (Erdos722.Generators.modCliqueBoundaryOn N r K Q) =
      Erdos722.Generators.modCliqueBoundaryOn N r
        (rotateFamily σ K) (rotateEdge σ Q) := by
  funext e
  unfold restrictedRotateAddEquiv
  simp only [Erdos722.Generators.modCliqueBoundaryOn, AddEquiv.coe_mk,
    Equiv.coe_fn_mk, rotateEdge_card]
  simp only [subset_rotateEdge_iff]

/-- Restricted modular span is invariant under relabelling. -/
theorem inRestrictedModularSpan_rotate
    {N r : ℕ} (σ : Equiv.Perm (Fin n))
    {K selected : Finset (Finset (Fin n))}
    {Q : Finset (Fin n)}
    (hspan : Erdos722.Generators.InRestrictedModularSpan
      N r K selected
        (Erdos722.Generators.modCliqueBoundaryOn N r K Q)) :
    Erdos722.Generators.InRestrictedModularSpan N r
      (rotateFamily σ K) (rotateFamily σ selected)
      (Erdos722.Generators.modCliqueBoundaryOn N r
        (rotateFamily σ K) (rotateEdge σ Q)) := by
  classical
  let oldVec := Erdos722.Generators.modCliqueBoundaryOn N r K
  let newVec := Erdos722.Generators.modCliqueBoundaryOn N r
    (rotateFamily σ K)
  let oldSet : Set (↑K → ZMod N) :=
    oldVec '' (↑selected : Set (Finset (Fin n)))
  let newSet : Set (↑(rotateFamily σ K) → ZMod N) :=
    newVec '' (↑(rotateFamily σ selected) : Set (Finset (Fin n)))
  let e := restrictedRotateAddEquiv N σ K
  have hmap : ∀ x, x ∈ AddSubgroup.closure oldSet →
      e x ∈ AddSubgroup.closure newSet := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
        obtain ⟨B, hB, rfl⟩ := hx
        apply AddSubgroup.subset_closure
        refine ⟨rotateEdge σ B, ?_, ?_⟩
        · apply mem_rotateFamily.mpr
          simpa using hB
        · simpa [e, oldVec, newVec] using
            (restrictedRotateAddEquiv_modCliqueBoundaryOn N r σ K B).symm
    | zero =>
        simpa using AddSubgroup.zero_mem (AddSubgroup.closure newSet)
    | add x y _hx _hy hx hy =>
        simpa using AddSubgroup.add_mem (AddSubgroup.closure newSet) hx hy
    | neg x _hx hx =>
        simpa using AddSubgroup.neg_mem (AddSubgroup.closure newSet) hx
  change Erdos722.Generators.modCliqueBoundaryOn N r K Q ∈
      AddSubgroup.closure oldSet at hspan
  change Erdos722.Generators.modCliqueBoundaryOn N r
      (rotateFamily σ K) (rotateEdge σ Q) ∈
        AddSubgroup.closure newSet
  rw [← restrictedRotateAddEquiv_modCliqueBoundaryOn]
  exact hmap _ hspan

/-! ## Equivariant two-cap prune data -/

/-- The part of the two-cap pruning output that is transported by every
colour permutation. -/
structure TwoCapPrunedData
    (N n q r faceCap edgeCap threshold Mface Medge : ℕ) where
  K : Finset (Finset (Fin n))
  selected : Finset (Finset (Fin n))
  Kstar : Finset (Finset (Fin n))
  uniform : ∀ e ∈ K, e.card = r
  selected_subset : selected ⊆
    Erdos722.IntegralGenerators.cliquesIn n q r K
  selected_card : selected.card ≤ N * K.card
  Kstar_subset : Kstar ⊆ K
  Kstar_eq : Kstar = Erdos722.Prune.prunedEdges r threshold K
    (Erdos722.IntegralGenerators.twoCapSaturatedCliques
      n q r faceCap edgeCap K selected)
  heavy_loss :
    faceCap * edgeCap * threshold *
        (Erdos722.Prune.heavyEdges r threshold K
          (Erdos722.IntegralGenerators.twoCapSaturatedCliques
            n q r faceCap edgeCap K selected)).card ≤
      (N * K.card) *
        (Nat.choose q (r - 1) * edgeCap * Mface +
          Nat.choose q r * faceCap * Medge) * Nat.choose q r
  face_load : ∀ f : Finset (Fin n), f.card = r - 1 →
    Erdos722.Generators.counterLoad
      (fun f Q : Finset (Fin n) ↦ f ⊆ Q) selected f ≤ faceCap
  edge_load : ∀ e : Finset (Fin n), e.card = r →
    Erdos722.Generators.counterLoad
      (fun e Q : Finset (Fin n) ↦ e ⊆ Q) selected e ≤ edgeCap
  good_lower : ∀ e ∈ Kstar,
    ((Erdos722.IntegralGenerators.cliquesIn n q r K).filter
        fun Q ↦ e ⊆ Q).card - threshold ≤
      ((Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
        n q r faceCap edgeCap K selected).filter fun Q ↦ e ⊆ Q).card
  selected_span : ∀ Q ∈
      Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
        n q r faceCap edgeCap K selected,
    Erdos722.Generators.InRestrictedModularSpan N r K selected
      (Erdos722.Generators.modCliqueBoundaryOn N r K Q)

/-- Package the relevant conclusions of the finite two-cap prune theorem. -/
theorem exists_twoCapPrunedData
    {N n q r faceCap edgeCap threshold Mface Medge : ℕ}
    (hN : 0 < N) (K : Finset (Finset (Fin n)))
    (huniform : ∀ e ∈ K, e.card = r)
    (hface : ∀ f ∈ Erdos722.Typicality.uniformEdges n (r - 1),
      ((Erdos722.IntegralGenerators.cliquesIn n q r K).filter
        fun Q ↦ f ⊆ Q).card ≤ Mface)
    (hedge : ∀ e ∈ Erdos722.Typicality.uniformEdges n r,
      ((Erdos722.IntegralGenerators.cliquesIn n q r K).filter
        fun Q ↦ e ⊆ Q).card ≤ Medge) :
    ∃ D : TwoCapPrunedData
        N n q r faceCap edgeCap threshold Mface Medge,
      D.K = K := by
  obtain ⟨selected, Kstar, hselected, hselectedCard, hKstar,
      hKstarEq, hfaceLoad, hedgeLoad, hsatFaces, hsatEdges, hsatCard,
      hheavy, hgood, hspan⟩ :=
    Erdos722.Prune.exists_twoCap_pruned_modular_generators
      hN K huniform hface hedge
  have hheavyLoss :=
    Erdos722.Prune.faceCap_mul_edgeCap_mul_threshold_mul_heavy_le
      hsatFaces hsatEdges hsatCard hheavy
  exact ⟨⟨K, selected, Kstar, huniform, hselected, hselectedCard,
    hKstar, hKstarEq, hheavyLoss, hfaceLoad, hedgeLoad, hgood, hspan⟩, rfl⟩

/-- If the division-free pruning loss is at most half of the available
edge mass, at least half of the base host survives. -/
theorem TwoCapPrunedData.card_K_le_two_mul_card_Kstar
    {N n q r faceCap edgeCap threshold Mface Medge : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (hfaceCap : 0 < faceCap) (hedgeCap : 0 < edgeCap)
    (hthreshold : 0 < threshold)
    (hloss :
      2 * ((N * D.K.card) *
        (Nat.choose q (r - 1) * edgeCap * Mface +
          Nat.choose q r * faceCap * Medge) * Nat.choose q r) ≤
        faceCap * edgeCap * threshold * D.K.card) :
    D.K.card ≤ 2 * D.Kstar.card := by
  let exceptional :=
    Erdos722.IntegralGenerators.twoCapSaturatedCliques
      n q r faceCap edgeCap D.K D.selected
  let heavy := Erdos722.Prune.heavyEdges r threshold D.K exceptional
  have hheavySubset : heavy ⊆ D.K := by
    exact Erdos722.Prune.heavyEdges_subset r threshold D.K exceptional
  have hscaled :
      faceCap * edgeCap * threshold * (2 * heavy.card) ≤
        faceCap * edgeCap * threshold * D.K.card := by
    calc
      faceCap * edgeCap * threshold * (2 * heavy.card) =
          2 * (faceCap * edgeCap * threshold * heavy.card) := by ring
      _ ≤ 2 * ((N * D.K.card) *
          (Nat.choose q (r - 1) * edgeCap * Mface +
            Nat.choose q r * faceCap * Medge) * Nat.choose q r) :=
        Nat.mul_le_mul_left 2 (by simpa [heavy, exceptional] using D.heavy_loss)
      _ ≤ faceCap * edgeCap * threshold * D.K.card := hloss
  have hcoefficient : 0 < faceCap * edgeCap * threshold := by positivity
  have hheavy : 2 * heavy.card ≤ D.K.card := by
    apply Nat.le_of_mul_le_mul_left (c := faceCap * edgeCap * threshold)
    · simpa [Nat.mul_assoc] using hscaled
    · exact hcoefficient
  have hcardStar : D.Kstar.card = D.K.card - heavy.card := by
    rw [D.Kstar_eq]
    simpa [Erdos722.Prune.prunedEdges, heavy, exceptional] using
      Finset.card_sdiff_of_subset hheavySubset
  omega

def TwoCapPrunedData.rotatedK
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u) :
    Finset (Finset (Fin n)) :=
  rotateFamily (σ i) D.K

def TwoCapPrunedData.rotatedSelected
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u) :
    Finset (Finset (Fin n)) :=
  rotateFamily (σ i) D.selected

def TwoCapPrunedData.rotatedKstar
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u) :
    Finset (Finset (Fin n)) :=
  rotateFamily (σ i) D.Kstar

lemma TwoCapPrunedData.rotatedSelected_subset
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u) :
    D.rotatedSelected σ i ⊆
      Erdos722.IntegralGenerators.cliquesIn n q r (D.rotatedK σ i) := by
  unfold TwoCapPrunedData.rotatedSelected TwoCapPrunedData.rotatedK
  rw [← rotateFamily_cliquesIn]
  exact rotateFamily_mono (σ i) D.selected_subset

lemma TwoCapPrunedData.rotated_face_load
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u)
    (f : Finset (Fin n)) (hf : f.card = r - 1) :
    Erdos722.Generators.counterLoad
      (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
      (D.rotatedSelected σ i) f ≤ faceCap := by
  let f₀ := rotateEdge (σ i).symm f
  have hf₀ : f₀.card = r - 1 := by simpa [f₀]
  have h := D.face_load f₀ hf₀
  have heq := counterLoad_rotateFamily (σ i) D.selected f₀
  calc
    Erdos722.Generators.counterLoad
        (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
        (D.rotatedSelected σ i) f =
      Erdos722.Generators.counterLoad
        (fun f Q : Finset (Fin n) ↦ f ⊆ Q)
        (rotateFamily (σ i) D.selected) (rotateEdge (σ i) f₀) := by
          simp [TwoCapPrunedData.rotatedSelected, f₀]
    _ = Erdos722.Generators.counterLoad
        (fun f Q : Finset (Fin n) ↦ f ⊆ Q) D.selected f₀ := heq
    _ ≤ faceCap := h

lemma TwoCapPrunedData.rotated_edge_load
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u)
    (e : Finset (Fin n)) (he : e.card = r) :
    Erdos722.Generators.counterLoad
      (fun e Q : Finset (Fin n) ↦ e ⊆ Q)
      (D.rotatedSelected σ i) e ≤ edgeCap := by
  let e₀ := rotateEdge (σ i).symm e
  have he₀ : e₀.card = r := by simpa [e₀]
  have h := D.edge_load e₀ he₀
  have heq := counterLoad_rotateFamily (σ i) D.selected e₀
  calc
    Erdos722.Generators.counterLoad
        (fun e Q : Finset (Fin n) ↦ e ⊆ Q)
        (D.rotatedSelected σ i) e =
      Erdos722.Generators.counterLoad
        (fun e Q : Finset (Fin n) ↦ e ⊆ Q)
        (rotateFamily (σ i) D.selected) (rotateEdge (σ i) e₀) := by
          simp [TwoCapPrunedData.rotatedSelected, e₀]
    _ = Erdos722.Generators.counterLoad
        (fun e Q : Finset (Fin n) ↦ e ⊆ Q) D.selected e₀ := heq
    _ ≤ edgeCap := h

lemma TwoCapPrunedData.rotated_selected_span
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData
      N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (i : Fin u)
    (Q : Finset (Fin n))
    (hQ : Q ∈ Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
      n q r faceCap edgeCap (D.rotatedK σ i)
        (D.rotatedSelected σ i)) :
    Erdos722.Generators.InRestrictedModularSpan N r
      (D.rotatedK σ i) (D.rotatedSelected σ i)
      (Erdos722.Generators.modCliqueBoundaryOn N r
        (D.rotatedK σ i) Q) := by
  let Q₀ := rotateEdge (σ i).symm Q
  have hQ₀ : Q₀ ∈
      Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
        n q r faceCap edgeCap D.K D.selected := by
    have hEq := rotateFamily_twoCapUnsaturatedCliques
      (σ i) D.K D.selected q r faceCap edgeCap
    have hrot : rotateEdge (σ i) Q₀ = Q := by simp [Q₀]
    have : rotateEdge (σ i) Q₀ ∈ rotateFamily (σ i)
        (Erdos722.IntegralGenerators.twoCapUnsaturatedCliques
          n q r faceCap edgeCap D.K D.selected) := by
      rw [hEq]
      rw [hrot]
      simpa [TwoCapPrunedData.rotatedK,
        TwoCapPrunedData.rotatedSelected] using hQ
    exact mem_rotateFamily.mp (by simpa [hrot] using this)
  have hspan := inRestrictedModularSpan_rotate (σ i)
    (D.selected_span Q₀ hQ₀)
  simpa [TwoCapPrunedData.rotatedK,
    TwoCapPrunedData.rotatedSelected, Q₀] using hspan

/-- Permutations carrying `source` exactly to `target`. -/
def edgeFiber (source target : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦
    rotateEdge σ source = target

@[simp] lemma mem_edgeFiber {source target : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ edgeFiber source target ↔ rotateEdge σ source = target := by
  simp [edgeFiber]

/-- Fibres of the permutation action on finite sets depend only on the
cardinality of the source. -/
theorem card_edgeFiber_eq_of_card_eq
    {source₁ source₂ target : Finset (Fin n)}
    (hcard : source₁.card = source₂.card) :
    (edgeFiber source₁ target).card =
      (edgeFiber source₂ target).card := by
  classical
  obtain ⟨τ, hτ⟩ :=
    Equiv.Perm.exists_map_finset_eq source₂ source₁ hcard.symm
  change rotateEdge τ source₂ = source₁ at hτ
  apply Finset.card_bij'
    (s := edgeFiber source₁ target)
    (t := edgeFiber source₂ target)
    (fun σ _hσ ↦ τ.trans σ)
    (fun ρ _hρ ↦ τ.symm.trans ρ)
  · intro σ hσ
    apply mem_edgeFiber.mpr
    rw [rotateEdge_trans, hτ]
    exact mem_edgeFiber.mp hσ
  · intro ρ hρ
    apply mem_edgeFiber.mpr
    rw [rotateEdge_trans]
    have hτinv : rotateEdge τ.symm source₁ = source₂ := by
      rw [← hτ]
      exact rotateEdge_symm_rotateEdge τ source₂
    rw [hτinv]
    exact mem_edgeFiber.mp hρ
  · intro σ hσ
    ext x
    simp
  · intro ρ hρ
    ext x
    simp

/-- Rotations for which the inverse image of `target` belongs to `K`. -/
def hitPermutations (K : Finset (Finset (Fin n)))
    (target : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦
    rotateEdge σ.symm target ∈ K

@[simp] lemma mem_hitPermutations
    {K : Finset (Finset (Fin n))} {target : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ hitPermutations K target ↔ rotateEdge σ.symm target ∈ K := by
  simp [hitPermutations]

lemma hitPermutations_eq_biUnion_edgeFiber
    (K : Finset (Finset (Fin n))) (target : Finset (Fin n)) :
    hitPermutations K target = K.biUnion fun e ↦ edgeFiber e target := by
  classical
  ext σ
  constructor
  · intro hσ
    let e := rotateEdge σ.symm target
    apply Finset.mem_biUnion.mpr
    refine ⟨e, mem_hitPermutations.mp hσ, ?_⟩
    apply mem_edgeFiber.mpr
    dsimp [e]
    have := rotateEdge_symm_rotateEdge σ.symm target
    simpa using this
  · intro hσ
    obtain ⟨e, heK, heσ⟩ := Finset.mem_biUnion.mp hσ
    apply mem_hitPermutations.mpr
    have heq := mem_edgeFiber.mp heσ
    rw [← heq]
    simpa using heK

lemma edgeFiber_pairwiseDisjoint (target : Finset (Fin n)) :
    (Set.univ : Set (Finset (Fin n))).PairwiseDisjoint
      (fun e ↦ edgeFiber e target) := by
  intro e _he f _hf hef
  apply Finset.disjoint_left.mpr
  intro σ hσe hσf
  have he := mem_edgeFiber.mp hσe
  have hf := mem_edgeFiber.mp hσf
  apply hef
  apply σ.finsetCongr.injective
  simpa [rotateEdge] using he.trans hf.symm

/-- Exact one-edge rotation count, factored through the stabilizer fibre of
the target edge. -/
theorem card_hitPermutations_eq_mul_fiber
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target : Finset (Fin n)} (hK : ∀ e ∈ K, e.card = r)
    (htarget : target.card = r) :
    (hitPermutations K target).card =
      K.card * (edgeFiber target target).card := by
  classical
  rw [hitPermutations_eq_biUnion_edgeFiber,
    Finset.card_biUnion
      ((edgeFiber_pairwiseDisjoint target).subset (Set.subset_univ _))]
  calc
    (∑ e ∈ K, (edgeFiber e target).card) =
        ∑ _e ∈ K, (edgeFiber target target).card := by
      apply Finset.sum_congr rfl
      intro e he
      exact card_edgeFiber_eq_of_card_eq ((hK e he).trans htarget.symm)
    _ = K.card * (edgeFiber target target).card := by simp

lemma hitPermutations_uniform_eq_univ
    {r : ℕ} {target : Finset (Fin n)} (htarget : target.card = r) :
    hitPermutations (Erdos722.Typicality.uniformEdges n r) target =
      (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
  classical
  apply Finset.eq_univ_of_forall
  intro σ
  apply mem_hitPermutations.mpr
  exact Erdos722.Typicality.mem_uniformEdges.mpr (by
    simpa using (rotateEdge_card σ.symm target).trans htarget)

/-- Cross-multiplied form of the exact statement that the inverse image of
a fixed uniform edge is uniformly distributed over all uniform edges. -/
theorem card_hitPermutations_mul_choose
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target : Finset (Fin n)} (hK : ∀ e ∈ K, e.card = r)
    (htarget : target.card = r) :
    (hitPermutations K target).card * Nat.choose n r =
      K.card * Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hKcount := card_hitPermutations_eq_mul_fiber hK htarget
  have hallcount := card_hitPermutations_eq_mul_fiber
    (K := Erdos722.Typicality.uniformEdges n r)
    (target := target)
    (fun e he ↦ Erdos722.Typicality.mem_uniformEdges.mp he) htarget
  rw [hitPermutations_uniform_eq_univ htarget] at hallcount
  have huniformCard :
      (Erdos722.Typicality.uniformEdges n r).card = Nat.choose n r := by
    simp [Erdos722.Typicality.uniformEdges]
  rw [Finset.card_univ, huniformCard] at hallcount
  rw [hKcount]
  nlinarith

/-- The symmetric group is transitive on ordered pairs of disjoint finite
sets with prescribed component cardinalities. -/
theorem exists_rotateEdge_eq_pair_of_disjoint
    {source₁ source₂ target₁ target₂ : Finset (Fin n)}
    (hsource : Disjoint source₁ source₂)
    (htarget : Disjoint target₁ target₂)
    (hcard₁ : source₁.card = target₁.card)
    (hcard₂ : source₂.card = target₂.card) :
    ∃ σ : Equiv.Perm (Fin n),
      rotateEdge σ source₁ = target₁ ∧
        rotateEdge σ source₂ = target₂ := by
  classical
  let e₁ : ↑source₁ ≃ ↑target₁ :=
    Fintype.equivOfCardEq (by simpa using hcard₁)
  let e₂ : ↑source₂ ≃ ↑target₂ :=
    Fintype.equivOfCardEq (by simpa using hcard₂)
  let f : (↑source₁ ⊕ ↑source₂) → Fin n
    | Sum.inl x => x
    | Sum.inr x => x
  let g : (↑source₁ ⊕ ↑source₂) → Fin n
    | Sum.inl x => e₁ x
    | Sum.inr x => e₂ x
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exfalso
      change (a : Fin n) = (b : Fin n) at hab
      have ha₂ : (a : Fin n) ∈ source₂ := by
        rw [hab]
        exact b.property
      exact Finset.disjoint_left.mp hsource a.property ha₂
    · exfalso
      change (a : Fin n) = (b : Fin n) at hab
      have hb₂ : (b : Fin n) ∈ source₂ := by
        rw [hab.symm]
        exact a.property
      exact Finset.disjoint_left.mp hsource b.property hb₂
    · exact congrArg Sum.inr (Subtype.ext hab)
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (e₁.injective (Subtype.ext hab))
    · exfalso
      change (e₁ a : Fin n) = (e₂ b : Fin n) at hab
      have ha₂ : (e₁ a : Fin n) ∈ target₂ := by
        rw [hab]
        exact (e₂ b).property
      exact Finset.disjoint_left.mp htarget (e₁ a).property ha₂
    · exfalso
      change (e₂ a : Fin n) = (e₁ b : Fin n) at hab
      have hb₂ : (e₁ b : Fin n) ∈ target₂ := by
        rw [hab.symm]
        exact (e₂ a).property
      exact Finset.disjoint_left.mp htarget (e₁ b).property hb₂
    · exact congrArg Sum.inr (e₂.injective (Subtype.ext hab))
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro y hy
      change y ∈ source₁.map σ.toEmbedding at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
      have hm := hσ (Sum.inl ⟨x, hx⟩)
      change σ x = (e₁ ⟨x, hx⟩ : Fin n) at hm
      have hyval : y = (e₁ ⟨x, hx⟩ : Fin n) := hxy.symm.trans hm
      rw [hyval]
      exact (e₁ ⟨x, hx⟩).property
    · rw [rotateEdge_card, hcard₁]
  · apply Finset.eq_of_subset_of_card_le
    · intro y hy
      change y ∈ source₂.map σ.toEmbedding at hy
      obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
      have hm := hσ (Sum.inr ⟨x, hx⟩)
      change σ x = (e₂ ⟨x, hx⟩ : Fin n) at hm
      have hyval : y = (e₂ ⟨x, hx⟩ : Fin n) := hxy.symm.trans hm
      rw [hyval]
      exact (e₂ ⟨x, hx⟩).property
    · rw [rotateEdge_card, hcard₂]

/-- Simultaneously map a finite labelled collection of pairwise-disjoint
parts.  This is the convenient transitivity interface for intersection
types of ordered edge pairs. -/
theorem exists_rotateEdge_eq_parts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source target : ι → Finset (Fin n))
    (hsource : ∀ i j, i ≠ j → Disjoint (source i) (source j))
    (htarget : ∀ i j, i ≠ j → Disjoint (target i) (target j))
    (hcard : ∀ i, (source i).card = (target i).card) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, rotateEdge σ (source i) = target i := by
  classical
  let e : (i : ι) → ↑(source i) ≃ ↑(target i) := fun i ↦
    Fintype.equivOfCardEq (by simpa using hcard i)
  let f : ((i : ι) × ↑(source i)) → Fin n := fun z ↦ z.2
  let g : ((i : ι) × ↑(source i)) → Fin n := fun z ↦ e z.1 z.2
  have hf : Function.Injective f := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst j
      have hsub : x = y := Subtype.ext hxy
      subst y
      rfl
    · exfalso
      change (x : Fin n) = (y : Fin n) at hxy
      have hxi : (x : Fin n) ∈ source i := x.property
      have hxj : (x : Fin n) ∈ source j := by
        rw [hxy]
        exact y.property
      exact Finset.disjoint_left.mp (hsource i j hij) hxi hxj
  have hg : Function.Injective g := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    by_cases hij : i = j
    · subst j
      have hsub : x = y := (e i).injective (Subtype.ext hxy)
      subst y
      rfl
    · exfalso
      change (e i x : Fin n) = (e j y : Fin n) at hxy
      have hti : (e i x : Fin n) ∈ target i := (e i x).property
      have htj : (e i x : Fin n) ∈ target j := by
        rw [hxy]
        exact (e j y).property
      exact Finset.disjoint_left.mp (htarget i j hij) hti htj
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_⟩
  intro i
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    change y ∈ (source i).map σ.toEmbedding at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    have hm := hσ ⟨i, ⟨x, hx⟩⟩
    change σ x = (e i ⟨x, hx⟩ : Fin n) at hm
    have hyval : y = (e i ⟨x, hx⟩ : Fin n) := hxy.symm.trans hm
    rw [hyval]
    exact (e i ⟨x, hx⟩).property
  · rw [rotateEdge_card, hcard i]

lemma rotateEdge_inter (σ : Equiv.Perm (Fin n))
    (e f : Finset (Fin n)) :
    rotateEdge σ (e ∩ f) = rotateEdge σ e ∩ rotateEdge σ f := by
  ext x
  simp [rotateEdge]

lemma rotateEdge_sdiff (σ : Equiv.Perm (Fin n))
    (e f : Finset (Fin n)) :
    rotateEdge σ (e \ f) = rotateEdge σ e \ rotateEdge σ f := by
  ext x
  simp [rotateEdge]

lemma rotateEdge_union (σ : Equiv.Perm (Fin n))
    (e f : Finset (Fin n)) :
    rotateEdge σ (e ∪ f) = rotateEdge σ e ∪ rotateEdge σ f := by
  ext x
  simp [rotateEdge]

/-- The symmetric group is transitive on ordered pairs with fixed two
component cardinalities and fixed intersection cardinality. -/
theorem exists_rotateEdge_eq_pair_of_inter_card
    {source₁ source₂ target₁ target₂ : Finset (Fin n)}
    (hcard₁ : source₁.card = target₁.card)
    (hcard₂ : source₂.card = target₂.card)
    (hinter : (source₁ ∩ source₂).card =
      (target₁ ∩ target₂).card) :
    ∃ σ : Equiv.Perm (Fin n),
      rotateEdge σ source₁ = target₁ ∧
        rotateEdge σ source₂ = target₂ := by
  classical
  let source : Fin 3 → Finset (Fin n) := fun i ↦
    match i.1 with
    | 0 => source₁ ∩ source₂
    | 1 => source₁ \ source₂
    | _ => source₂ \ source₁
  let target : Fin 3 → Finset (Fin n) := fun i ↦
    match i.1 with
    | 0 => target₁ ∩ target₂
    | 1 => target₁ \ target₂
    | _ => target₂ \ target₁
  have hsource : ∀ i j, i ≠ j → Disjoint (source i) (source j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [source, Finset.disjoint_left]
  have htarget : ∀ i j, i ≠ j → Disjoint (target i) (target j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [target, Finset.disjoint_left]
  have hinter' : (source₂ ∩ source₁).card =
      (target₂ ∩ target₁).card := by
    simpa [Finset.inter_comm] using hinter
  have hcards : ∀ i, (source i).card = (target i).card := by
    intro i
    have hi : i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 := by omega
    rcases hi with hi | hi | hi
    · have hieq : i = (0 : Fin 3) := Fin.ext hi
      subst i
      simpa [source, target] using hinter
    · have hieq : i = (1 : Fin 3) := Fin.ext hi
      subst i
      change (source₁ \ source₂).card = (target₁ \ target₂).card
      simp only [Finset.card_sdiff]
      rw [hcard₁, hinter']
    · have hieq : i = (2 : Fin 3) := Fin.ext hi
      subst i
      change (source₂ \ source₁).card = (target₂ \ target₁).card
      simp only [Finset.card_sdiff]
      rw [hcard₂, hinter]
  obtain ⟨σ, hσ⟩ := exists_rotateEdge_eq_parts source target
    hsource htarget hcards
  have h₀ := hσ (0 : Fin 3)
  have h₁ := hσ (1 : Fin 3)
  have h₂ := hσ (2 : Fin 3)
  change rotateEdge σ (source₁ ∩ source₂) =
    target₁ ∩ target₂ at h₀
  change rotateEdge σ (source₁ \ source₂) =
    target₁ \ target₂ at h₁
  change rotateEdge σ (source₂ \ source₁) =
    target₂ \ target₁ at h₂
  refine ⟨σ, ?_, ?_⟩
  · rw [show source₁ =
        (source₁ ∩ source₂) ∪ (source₁ \ source₂) by
          rw [Finset.union_comm, Finset.sdiff_union_inter],
      rotateEdge_union, h₀, h₁]
    rw [Finset.union_comm, Finset.sdiff_union_inter]
  · rw [show source₂ =
        (source₁ ∩ source₂) ∪ (source₂ \ source₁) by
          rw [Finset.inter_comm, Finset.union_comm,
            Finset.sdiff_union_inter],
      rotateEdge_union, h₀, h₂]
    rw [Finset.inter_comm, Finset.union_comm,
      Finset.sdiff_union_inter]

/-- Permutations carrying an ordered source pair to an ordered target pair. -/
def edgePairFiber (source₁ source₂ target₁ target₂ :
    Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦
    rotateEdge σ source₁ = target₁ ∧
      rotateEdge σ source₂ = target₂

@[simp] lemma mem_edgePairFiber
    {source₁ source₂ target₁ target₂ : Finset (Fin n)}
    {σ : Equiv.Perm (Fin n)} :
    σ ∈ edgePairFiber source₁ source₂ target₁ target₂ ↔
      rotateEdge σ source₁ = target₁ ∧
        rotateEdge σ source₂ = target₂ := by
  simp [edgePairFiber]

/-- Pair-action fibres are constant on ordered disjoint pairs of fixed
component cardinalities. -/
theorem card_edgePairFiber_eq_of_disjoint
    {source₁ source₂ source₁' source₂' target₁ target₂ :
      Finset (Fin n)}
    (hsource : Disjoint source₁ source₂)
    (hsource' : Disjoint source₁' source₂')
    (hcard₁ : source₁.card = source₁'.card)
    (hcard₂ : source₂.card = source₂'.card) :
    (edgePairFiber source₁ source₂ target₁ target₂).card =
      (edgePairFiber source₁' source₂' target₁ target₂).card := by
  classical
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_rotateEdge_eq_pair_of_disjoint
    hsource' hsource hcard₁.symm hcard₂.symm
  apply Finset.card_bij'
    (s := edgePairFiber source₁ source₂ target₁ target₂)
    (t := edgePairFiber source₁' source₂' target₁ target₂)
    (fun σ _hσ ↦ τ.trans σ)
    (fun ρ _hρ ↦ τ.symm.trans ρ)
  · intro σ hσ
    apply mem_edgePairFiber.mpr
    have hσdata := mem_edgePairFiber.mp hσ
    constructor <;> rw [rotateEdge_trans]
    · rw [hτ₁]
      exact hσdata.1
    · rw [hτ₂]
      exact hσdata.2
  · intro ρ hρ
    apply mem_edgePairFiber.mpr
    have hρdata := mem_edgePairFiber.mp hρ
    have hτinv₁ : rotateEdge τ.symm source₁ = source₁' := by
      rw [← hτ₁]
      exact rotateEdge_symm_rotateEdge τ source₁'
    have hτinv₂ : rotateEdge τ.symm source₂ = source₂' := by
      rw [← hτ₂]
      exact rotateEdge_symm_rotateEdge τ source₂'
    constructor <;> rw [rotateEdge_trans]
    · rw [hτinv₁]
      exact hρdata.1
    · rw [hτinv₂]
      exact hρdata.2
  · intro σ hσ
    ext x
    simp
  · intro ρ hρ
    ext x
    simp

/-- Pair-action fibres are constant on the full intersection type of the
ordered source pair. -/
theorem card_edgePairFiber_eq_of_inter_card
    {source₁ source₂ source₁' source₂' target₁ target₂ :
      Finset (Fin n)}
    (hcard₁ : source₁.card = source₁'.card)
    (hcard₂ : source₂.card = source₂'.card)
    (hinter : (source₁ ∩ source₂).card =
      (source₁' ∩ source₂').card) :
    (edgePairFiber source₁ source₂ target₁ target₂).card =
      (edgePairFiber source₁' source₂' target₁ target₂).card := by
  classical
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_rotateEdge_eq_pair_of_inter_card
    hcard₁.symm hcard₂.symm hinter.symm
  apply Finset.card_bij'
    (s := edgePairFiber source₁ source₂ target₁ target₂)
    (t := edgePairFiber source₁' source₂' target₁ target₂)
    (fun σ _hσ ↦ τ.trans σ)
    (fun ρ _hρ ↦ τ.symm.trans ρ)
  · intro σ hσ
    apply mem_edgePairFiber.mpr
    have hσdata := mem_edgePairFiber.mp hσ
    constructor <;> rw [rotateEdge_trans]
    · rw [hτ₁]
      exact hσdata.1
    · rw [hτ₂]
      exact hσdata.2
  · intro ρ hρ
    apply mem_edgePairFiber.mpr
    have hρdata := mem_edgePairFiber.mp hρ
    have hτinv₁ : rotateEdge τ.symm source₁ = source₁' := by
      rw [← hτ₁]
      exact rotateEdge_symm_rotateEdge τ source₁'
    have hτinv₂ : rotateEdge τ.symm source₂ = source₂' := by
      rw [← hτ₂]
      exact rotateEdge_symm_rotateEdge τ source₂'
    constructor <;> rw [rotateEdge_trans]
    · rw [hτinv₁]
      exact hρdata.1
    · rw [hτinv₂]
      exact hρdata.2
  · intro σ hσ
    ext x
    simp
  · intro ρ hρ
    ext x
    simp

/-- Ordered disjoint edge pairs drawn from a family. -/
def orderedDisjointPairs (K : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (K ×ˢ K).filter fun p ↦ Disjoint p.1 p.2

@[simp] lemma mem_orderedDisjointPairs
    {K : Finset (Finset (Fin n))}
    {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ orderedDisjointPairs K ↔
      p.1 ∈ K ∧ p.2 ∈ K ∧ Disjoint p.1 p.2 := by
  simp [orderedDisjointPairs, and_assoc]

/-- Ordered edge pairs of one prescribed intersection cardinality. -/
def orderedIntersectionPairs (K : Finset (Finset (Fin n))) (j : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (K ×ˢ K).filter fun p ↦ (p.1 ∩ p.2).card = j

@[simp] lemma mem_orderedIntersectionPairs
    {K : Finset (Finset (Fin n))} {j : ℕ}
    {p : Finset (Fin n) × Finset (Fin n)} :
    p ∈ orderedIntersectionPairs K j ↔
      p.1 ∈ K ∧ p.2 ∈ K ∧ (p.1 ∩ p.2).card = j := by
  simp [orderedIntersectionPairs, and_assoc]

/-- Rotations for which the inverse images of two target edges are a
disjoint ordered pair in `K`. -/
def pairHitPermutations (K : Finset (Finset (Fin n)))
    (target₁ target₂ : Finset (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter fun σ ↦
    rotateEdge σ.symm target₁ ∈ K ∧
      rotateEdge σ.symm target₂ ∈ K

@[simp] lemma mem_pairHitPermutations
    {K : Finset (Finset (Fin n))}
    {target₁ target₂ : Finset (Fin n)} {σ : Equiv.Perm (Fin n)} :
    σ ∈ pairHitPermutations K target₁ target₂ ↔
      rotateEdge σ.symm target₁ ∈ K ∧
        rotateEdge σ.symm target₂ ∈ K := by
  simp [pairHitPermutations]

lemma pairHitPermutations_eq_biUnion_edgePairFiber
    (K : Finset (Finset (Fin n)))
    {target₁ target₂ : Finset (Fin n)}
    (htarget : Disjoint target₁ target₂) :
    pairHitPermutations K target₁ target₂ =
      (orderedDisjointPairs K).biUnion fun p ↦
        edgePairFiber p.1 p.2 target₁ target₂ := by
  classical
  ext σ
  constructor
  · intro hσ
    let e₁ := rotateEdge σ.symm target₁
    let e₂ := rotateEdge σ.symm target₂
    have hedisjoint : Disjoint e₁ e₂ := by
      have he₁map : rotateEdge σ e₁ = target₁ := by
        dsimp [e₁]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₁
      have he₂map : rotateEdge σ e₂ = target₂ := by
        dsimp [e₂]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₂
      apply Finset.disjoint_left.mpr
      intro x hx₁ hx₂
      have hσx₁ : σ x ∈ target₁ := by
        rw [← he₁map]
        change σ x ∈ e₁.map σ.toEmbedding
        exact Finset.mem_map.mpr ⟨x, hx₁, rfl⟩
      have hσx₂ : σ x ∈ target₂ := by
        rw [← he₂map]
        change σ x ∈ e₂.map σ.toEmbedding
        exact Finset.mem_map.mpr ⟨x, hx₂, rfl⟩
      exact Finset.disjoint_left.mp htarget hσx₁ hσx₂
    apply Finset.mem_biUnion.mpr
    refine ⟨(e₁, e₂), ?_, ?_⟩
    · exact mem_orderedDisjointPairs.mpr
        ⟨(mem_pairHitPermutations.mp hσ).1,
          (mem_pairHitPermutations.mp hσ).2, hedisjoint⟩
    · apply mem_edgePairFiber.mpr
      constructor
      · dsimp [e₁]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₁
      · dsimp [e₂]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₂
  · intro hσ
    obtain ⟨p, hp, hσp⟩ := Finset.mem_biUnion.mp hσ
    have hpdata := mem_orderedDisjointPairs.mp hp
    have hmap := mem_edgePairFiber.mp hσp
    apply mem_pairHitPermutations.mpr
    constructor
    · rw [← hmap.1]
      simpa using hpdata.1
    · rw [← hmap.2]
      simpa using hpdata.2.1

lemma pairHitPermutations_eq_biUnion_intersectionFiber
    (K : Finset (Finset (Fin n)))
    (target₁ target₂ : Finset (Fin n)) :
    pairHitPermutations K target₁ target₂ =
      (orderedIntersectionPairs K (target₁ ∩ target₂).card).biUnion
        fun p ↦ edgePairFiber p.1 p.2 target₁ target₂ := by
  classical
  ext σ
  constructor
  · intro hσ
    let e₁ := rotateEdge σ.symm target₁
    let e₂ := rotateEdge σ.symm target₂
    have hinter : (e₁ ∩ e₂).card = (target₁ ∩ target₂).card := by
      rw [← rotateEdge_inter]
      exact rotateEdge_card σ.symm (target₁ ∩ target₂)
    apply Finset.mem_biUnion.mpr
    refine ⟨(e₁, e₂), ?_, ?_⟩
    · exact mem_orderedIntersectionPairs.mpr
        ⟨(mem_pairHitPermutations.mp hσ).1,
          (mem_pairHitPermutations.mp hσ).2, hinter⟩
    · apply mem_edgePairFiber.mpr
      constructor
      · dsimp [e₁]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₁
      · dsimp [e₂]
        simpa using rotateEdge_symm_rotateEdge σ.symm target₂
  · intro hσ
    obtain ⟨p, hp, hσp⟩ := Finset.mem_biUnion.mp hσ
    have hpdata := mem_orderedIntersectionPairs.mp hp
    have hmap := mem_edgePairFiber.mp hσp
    apply mem_pairHitPermutations.mpr
    constructor
    · rw [← hmap.1]
      simpa using hpdata.1
    · rw [← hmap.2]
      simpa using hpdata.2.1

lemma edgePairFiber_pairwiseDisjoint
    (target₁ target₂ : Finset (Fin n)) :
    (Set.univ : Set (Finset (Fin n) × Finset (Fin n))).PairwiseDisjoint
      (fun p ↦ edgePairFiber p.1 p.2 target₁ target₂) := by
  intro p _hp q _hq hpq
  apply Finset.disjoint_left.mpr
  intro σ hσp hσq
  have hp := mem_edgePairFiber.mp hσp
  have hq := mem_edgePairFiber.mp hσq
  apply hpq
  apply Prod.ext
  · apply σ.finsetCongr.injective
    simpa [rotateEdge] using hp.1.trans hq.1.symm
  · apply σ.finsetCongr.injective
    simpa [rotateEdge] using hp.2.trans hq.2.symm

/-- Exact two-edge rotation count, factored through one canonical disjoint
pair fibre. -/
theorem card_pairHitPermutations_eq_mul_fiber
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target₁ target₂ : Finset (Fin n)}
    (hK : ∀ e ∈ K, e.card = r)
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r)
    (htarget : Disjoint target₁ target₂) :
    (pairHitPermutations K target₁ target₂).card =
      (orderedDisjointPairs K).card *
        (edgePairFiber target₁ target₂ target₁ target₂).card := by
  classical
  rw [pairHitPermutations_eq_biUnion_edgePairFiber K htarget,
    Finset.card_biUnion
      ((edgePairFiber_pairwiseDisjoint target₁ target₂).subset
        (Set.subset_univ _))]
  calc
    (∑ p ∈ orderedDisjointPairs K,
        (edgePairFiber p.1 p.2 target₁ target₂).card) =
        ∑ _p ∈ orderedDisjointPairs K,
          (edgePairFiber target₁ target₂ target₁ target₂).card := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpdata := mem_orderedDisjointPairs.mp hp
      apply card_edgePairFiber_eq_of_disjoint hpdata.2.2 htarget
      · exact (hK p.1 hpdata.1).trans htarget₁.symm
      · exact (hK p.2 hpdata.2.1).trans htarget₂.symm
    _ = (orderedDisjointPairs K).card *
        (edgePairFiber target₁ target₂ target₁ target₂).card := by
      simp

/-- General fixed-intersection version of the exact two-edge rotation
count. -/
theorem card_pairHitPermutations_eq_mul_intersectionFiber
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target₁ target₂ : Finset (Fin n)}
    (hK : ∀ e ∈ K, e.card = r)
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r) :
    (pairHitPermutations K target₁ target₂).card =
      (orderedIntersectionPairs K (target₁ ∩ target₂).card).card *
        (edgePairFiber target₁ target₂ target₁ target₂).card := by
  classical
  rw [pairHitPermutations_eq_biUnion_intersectionFiber,
    Finset.card_biUnion
      ((edgePairFiber_pairwiseDisjoint target₁ target₂).subset
        (Set.subset_univ _))]
  calc
    (∑ p ∈ orderedIntersectionPairs K (target₁ ∩ target₂).card,
        (edgePairFiber p.1 p.2 target₁ target₂).card) =
        ∑ _p ∈ orderedIntersectionPairs K (target₁ ∩ target₂).card,
          (edgePairFiber target₁ target₂ target₁ target₂).card := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpdata := mem_orderedIntersectionPairs.mp hp
      apply card_edgePairFiber_eq_of_inter_card
      · exact (hK p.1 hpdata.1).trans htarget₁.symm
      · exact (hK p.2 hpdata.2.1).trans htarget₂.symm
      · exact hpdata.2.2
    _ = (orderedIntersectionPairs K (target₁ ∩ target₂).card).card *
        (edgePairFiber target₁ target₂ target₁ target₂).card := by
      simp

lemma pairHitPermutations_uniform_eq_univ
    {r : ℕ} {target₁ target₂ : Finset (Fin n)}
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r) :
    pairHitPermutations (Erdos722.Typicality.uniformEdges n r)
        target₁ target₂ =
      (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
  classical
  apply Finset.eq_univ_of_forall
  intro σ
  apply mem_pairHitPermutations.mpr
  constructor
  · exact Erdos722.Typicality.mem_uniformEdges.mpr (by
      simpa using (rotateEdge_card σ.symm target₁).trans htarget₁)
  · exact Erdos722.Typicality.mem_uniformEdges.mpr (by
      simpa using (rotateEdge_card σ.symm target₂).trans htarget₂)

/-- Cross-multiplied exact distribution law for ordered disjoint edge
pairs. -/
theorem card_pairHitPermutations_mul_uniformPairs
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target₁ target₂ : Finset (Fin n)}
    (hK : ∀ e ∈ K, e.card = r)
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r)
    (htarget : Disjoint target₁ target₂) :
    (pairHitPermutations K target₁ target₂).card *
        (orderedDisjointPairs
          (Erdos722.Typicality.uniformEdges n r)).card =
      (orderedDisjointPairs K).card *
        Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hKcount := card_pairHitPermutations_eq_mul_fiber hK
    htarget₁ htarget₂ htarget
  have hallcount := card_pairHitPermutations_eq_mul_fiber
    (K := Erdos722.Typicality.uniformEdges n r)
    (target₁ := target₁) (target₂ := target₂)
    (fun e he ↦ Erdos722.Typicality.mem_uniformEdges.mp he)
    htarget₁ htarget₂ htarget
  rw [pairHitPermutations_uniform_eq_univ htarget₁ htarget₂,
    Finset.card_univ] at hallcount
  rw [hKcount]
  nlinarith

/-- Cross-multiplied exact distribution law for arbitrary fixed
intersection type. -/
theorem card_pairHitPermutations_mul_uniformIntersectionPairs
    {r : ℕ} {K : Finset (Finset (Fin n))}
    {target₁ target₂ : Finset (Fin n)}
    (hK : ∀ e ∈ K, e.card = r)
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r) :
    (pairHitPermutations K target₁ target₂).card *
        (orderedIntersectionPairs
          (Erdos722.Typicality.uniformEdges n r)
          (target₁ ∩ target₂).card).card =
      (orderedIntersectionPairs K (target₁ ∩ target₂).card).card *
        Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  have hKcount := card_pairHitPermutations_eq_mul_intersectionFiber hK
    htarget₁ htarget₂
  have hallcount := card_pairHitPermutations_eq_mul_intersectionFiber
    (K := Erdos722.Typicality.uniformEdges n r)
    (target₁ := target₁) (target₂ := target₂)
    (fun e he ↦ Erdos722.Typicality.mem_uniformEdges.mp he)
    htarget₁ htarget₂
  rw [pairHitPermutations_uniform_eq_univ htarget₁ htarget₂,
    Finset.card_univ] at hallcount
  rw [hKcount]
  nlinarith

lemma uniformEdges_disjoint_filter_eq_powersetCard_sdiff
    {r : ℕ} (e : Finset (Fin n)) :
    (Erdos722.Typicality.uniformEdges n r).filter (Disjoint e) =
      ((Finset.univ : Finset (Fin n)) \ e).powersetCard r := by
  classical
  ext f
  simp only [Finset.mem_filter, Erdos722.Typicality.mem_uniformEdges,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨hfcard, hdisj⟩
    refine ⟨?_, hfcard⟩
    intro x hxf
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x,
      fun hxe ↦ Finset.disjoint_left.mp hdisj hxe hxf⟩
  · rintro ⟨hfsub, hfcard⟩
    refine ⟨hfcard, Finset.disjoint_left.mpr ?_⟩
    intro x hxe hxf
    exact (Finset.mem_sdiff.mp (hfsub hxf)).2 hxe

lemma card_uniformEdges_disjoint_filter
    {r : ℕ} {e : Finset (Fin n)} (hecard : e.card = r) :
    ((Erdos722.Typicality.uniformEdges n r).filter (Disjoint e)).card =
      Nat.choose (n - r) r := by
  rw [uniformEdges_disjoint_filter_eq_powersetCard_sdiff,
    Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ e),
    Finset.card_univ, hecard]
  simp

lemma card_orderedDisjointPairs_uniform :
    (orderedDisjointPairs
      (Erdos722.Typicality.uniformEdges n r)).card =
      Nat.choose n r * Nat.choose (n - r) r := by
  classical
  let U := Erdos722.Typicality.uniformEdges n r
  let P := orderedDisjointPairs U
  have hmaps : (P : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
      Prod.fst U := by
    intro p hp
    exact (mem_orderedDisjointPairs.mp hp).1
  rw [show (orderedDisjointPairs U).card = P.card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ e ∈ U,
      ((P.filter fun p ↦ p.1 = e).card) =
        (U.filter (Disjoint e)).card := by
    intro e he
    apply Finset.card_bij
      (s := P.filter fun p ↦ p.1 = e)
      (t := U.filter (Disjoint e))
      (fun p _hp ↦ p.2)
    · intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpair := mem_orderedDisjointPairs.mp hpdata.1
      have hp₁ : p.1 = e := hpdata.2
      exact Finset.mem_filter.mpr
        ⟨hpair.2.1, by simpa [hp₁] using hpair.2.2⟩
    · intro p hp q hq hpq
      have hp₁ := (Finset.mem_filter.mp hp).2
      have hq₁ := (Finset.mem_filter.mp hq).2
      apply Prod.ext
      · exact hp₁.trans hq₁.symm
      · exact hpq
    · intro f hf
      have hfdata := Finset.mem_filter.mp hf
      refine ⟨(e, f), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_orderedDisjointPairs.mpr
        ⟨he, hfdata.1, hfdata.2⟩, rfl⟩
  calc
    (∑ e ∈ U, ((P.filter fun p ↦ p.1 = e).card)) =
        ∑ _e ∈ U, Nat.choose (n - r) r := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hfiber e he]
      exact card_uniformEdges_disjoint_filter
        (Erdos722.Typicality.mem_uniformEdges.mp he)
    _ = U.card * Nat.choose (n - r) r := by simp
    _ = Nat.choose n r * Nat.choose (n - r) r := by
      simp [U, Erdos722.Typicality.uniformEdges]

/-- For a fixed `r`-edge, the number of `r`-edges meeting it in exactly
`j` vertices is the product obtained by choosing the vertices inside and
outside the fixed edge. -/
lemma card_uniformEdges_inter_filter
    {r j : ℕ} {e : Finset (Fin n)} (hecard : e.card = r)
    (hj : j ≤ r) :
    ((Erdos722.Typicality.uniformEdges n r).filter
        fun f ↦ (e ∩ f).card = j).card =
      Nat.choose r j * Nat.choose (n - r) (r - j) := by
  classical
  let U := Erdos722.Typicality.uniformEdges n r
  let S := U.filter fun f ↦ (e ∩ f).card = j
  let T := e.powersetCard j ×ˢ
    ((Finset.univ : Finset (Fin n)) \ e).powersetCard (r - j)
  have hreconstruct (f : Finset (Fin n)) :
      (e ∩ f) ∪ (f \ e) = f := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have houtside (I O : Finset (Fin n)) (hIe : I ⊆ e)
      (hOe : O ⊆ (Finset.univ : Finset (Fin n)) \ e) :
      e ∩ (I ∪ O) = I ∧ (I ∪ O) \ e = O := by
    constructor <;> ext x
    · simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxe, hxi | hxo⟩
        · exact hxi
        · exact False.elim ((Finset.mem_sdiff.mp (hOe hxo)).2 hxe)
      · intro hxi
        exact ⟨hIe hxi, Or.inl hxi⟩
    · simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxi | hxo, hne⟩
        · exact False.elim (hne (hIe hxi))
        · exact hxo
      · intro hxo
        exact ⟨Or.inr hxo, (Finset.mem_sdiff.mp (hOe hxo)).2⟩
  have hcardT : T.card =
      Nat.choose r j * Nat.choose (n - r) (r - j) := by
    have hunivdiff :
        ((Finset.univ : Finset (Fin n)) \ e).card = n - r := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ e),
        Finset.card_univ, hecard]
      simp
    simp [T, hecard, hunivdiff]
  rw [show
    ((Erdos722.Typicality.uniformEdges n r).filter
        fun f ↦ (e ∩ f).card = j).card = S.card by rfl,
    show Nat.choose r j * Nat.choose (n - r) (r - j) = T.card by
      exact hcardT.symm]
  apply Finset.card_bij
    (s := S) (t := T)
    (fun f _hf ↦ (e ∩ f, f \ e))
  · intro f hf
    have hfdata := Finset.mem_filter.mp hf
    have hfcard := Erdos722.Typicality.mem_uniformEdges.mp hfdata.1
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr
        ⟨Finset.inter_subset_left, hfdata.2⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hxf
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hxf).2⟩
      · have hsum := Finset.card_sdiff_add_card_inter f e
        have hinter : (f ∩ e).card = j := by
          rw [Finset.inter_comm]
          exact hfdata.2
        have hsdiff : (f \ e).card = r - j := by
          omega
        exact hsdiff
  · intro f hf g hg hfg
    have hfirst : e ∩ f = e ∩ g := congrArg Prod.fst hfg
    have hsecond : f \ e = g \ e := congrArg Prod.snd hfg
    rw [← hreconstruct f, ← hreconstruct g, hfirst, hsecond]
  · intro p hp
    have hpdata := Finset.mem_product.mp hp
    have hI := Finset.mem_powersetCard.mp hpdata.1
    have hO := Finset.mem_powersetCard.mp hpdata.2
    let f := p.1 ∪ p.2
    have hout := houtside p.1 p.2 hI.1 hO.1
    have hdisj : Disjoint p.1 p.2 := by
      apply Finset.disjoint_left.mpr
      intro x hxI hxO
      exact (Finset.mem_sdiff.mp (hO.1 hxO)).2 (hI.1 hxI)
    have hfcard : f.card = r := by
      dsimp [f]
      rw [Finset.card_union_of_disjoint hdisj, hI.2, hO.2]
      omega
    refine ⟨f, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Erdos722.Typicality.mem_uniformEdges.mpr hfcard, ?_⟩
      rw [show e ∩ f = p.1 by exact hout.1]
      exact hI.2
    · apply Prod.ext
      · exact hout.1
      · exact hout.2

/-- Exact cardinality of ordered pairs of uniform `r`-edges with prescribed
intersection size. -/
lemma card_orderedIntersectionPairs_uniform
    {r j : ℕ} (hj : j ≤ r) :
    (orderedIntersectionPairs
      (Erdos722.Typicality.uniformEdges n r) j).card =
      Nat.choose n r *
        (Nat.choose r j * Nat.choose (n - r) (r - j)) := by
  classical
  let U := Erdos722.Typicality.uniformEdges n r
  let P := orderedIntersectionPairs U j
  have hmaps : (P : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
      Prod.fst U := by
    intro p hp
    exact (mem_orderedIntersectionPairs.mp hp).1
  rw [show (orderedIntersectionPairs U j).card = P.card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ e ∈ U,
      (P.filter fun p ↦ p.1 = e).card =
        (U.filter fun f ↦ (e ∩ f).card = j).card := by
    intro e he
    apply Finset.card_bij
      (s := P.filter fun p ↦ p.1 = e)
      (t := U.filter fun f ↦ (e ∩ f).card = j)
      (fun p _hp ↦ p.2)
    · intro p hp
      have hpdata := Finset.mem_filter.mp hp
      have hpair := mem_orderedIntersectionPairs.mp hpdata.1
      exact Finset.mem_filter.mpr
        ⟨hpair.2.1, by simpa [hpdata.2] using hpair.2.2⟩
    · intro p hp q hq hpq
      have hp₁ := (Finset.mem_filter.mp hp).2
      have hq₁ := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hp₁.trans hq₁.symm) hpq
    · intro f hf
      have hfdata := Finset.mem_filter.mp hf
      refine ⟨(e, f), ?_, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨mem_orderedIntersectionPairs.mpr
          ⟨he, hfdata.1, hfdata.2⟩, rfl⟩
  calc
    (∑ e ∈ U, (P.filter fun p ↦ p.1 = e).card) =
        ∑ _e ∈ U,
          (Nat.choose r j * Nat.choose (n - r) (r - j)) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hfiber e he]
      exact card_uniformEdges_inter_filter
        (Erdos722.Typicality.mem_uniformEdges.mp he) hj
    _ = U.card *
        (Nat.choose r j * Nat.choose (n - r) (r - j)) := by simp
    _ = Nat.choose n r *
        (Nat.choose r j * Nat.choose (n - r) (r - j)) := by
      simp [U, Erdos722.Typicality.uniformEdges]

/-- A bound on codimension-one degrees controls every strictly smaller
face degree by charging each edge through the face to one of its
codimension-one subedges. -/
theorem localDegree_le_choose_mul_of_codimOneDegree
    {r j D : ℕ} (hr : 0 < r) {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hdeg : ∀ I : Finset (Fin n), I.card = r - 1 →
      (K.filter fun e ↦ I ⊆ e).card ≤ D)
    {J : Finset (Fin n)} (hJcard : J.card = j) (hj : j < r) :
    (K.filter fun e ↦ J ⊆ e).card ≤
      Nat.choose (n - j) (r - 1 - j) * D := by
  classical
  let left := K.filter fun e ↦ J ⊆ e
  let right :=
    (Erdos722.Typicality.uniformEdges n (r - 1)).filter fun I ↦ J ⊆ I
  have hcount := Erdos722.Reserve.card_mul_le_card_mul_of_relation
    left right (fun e I ↦ I ⊆ e) 1
    D (by
      intro e he
      have hedata := Finset.mem_filter.mp he
      have hecard := hK e hedata.1
      have heq : (right.filter fun I ↦ I ⊆ e) =
          (e.powersetCard (r - 1)).filter fun I ↦ J ⊆ I := by
        ext I
        simp only [right, Finset.mem_filter,
          Erdos722.Typicality.mem_uniformEdges,
          Finset.mem_powersetCard]
        aesop
      rw [heq, Finset.card_filter_powersetCard_subset J e (r - 1)
        hedata.2 (by omega), hecard, hJcard]
      exact Nat.choose_pos (by omega)) (by
      intro I hI
      have hIdata := Finset.mem_filter.mp hI
      have hIcard :=
        Erdos722.Typicality.mem_uniformEdges.mp hIdata.1
      have hsub : (left.filter fun e ↦ I ⊆ e) ⊆
          K.filter fun e ↦ I ⊆ e := by
        intro e he
        have hedata := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hedata.1).1, hedata.2⟩
      exact (Finset.card_le_card hsub).trans
        (hdeg I hIcard))
  have hrightcard : right.card =
      Nat.choose (n - j) (r - 1 - j) := by
    have heq : right =
        ((Finset.univ : Finset (Fin n)).powersetCard (r - 1)).filter
          (J ⊆ ·) := by rfl
    rw [heq, Finset.card_filter_powersetCard_subset J Finset.univ (r - 1)
      (Finset.subset_univ J) (by omega)]
    simp [hJcard]
  have hleft : left.card = (K.filter fun e ↦ J ⊆ e).card := by rfl
  rw [hleft, hrightcard] at hcount
  simpa using hcount

/-- The codimension-one cap bounds the number of members of a uniform
family having a prescribed intersection size with a fixed edge. -/
theorem card_intersection_filter_le_of_codimOneDegree
    {r j D : ℕ} (hr : 0 < r) {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hdeg : ∀ I : Finset (Fin n), I.card = r - 1 →
      (K.filter fun e ↦ I ⊆ e).card ≤ D)
    {e : Finset (Fin n)} (hecard : e.card = r) (hj : j < r) :
    (K.filter fun f ↦ (e ∩ f).card = j).card ≤
      Nat.choose r j *
        (Nat.choose (n - j) (r - 1 - j) * D) := by
  classical
  let S := K.filter fun f ↦ (e ∩ f).card = j
  let R := e.powersetCard j
  let π : Finset (Fin n) → Finset (Fin n) := fun f ↦ e ∩ f
  have hmaps : (S : Set (Finset (Fin n))).MapsTo π R := by
    intro f hf
    have hfdata := Finset.mem_filter.mp hf
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.inter_subset_left, hfdata.2⟩
  rw [show (K.filter fun f ↦ (e ∩ f).card = j).card = S.card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ J ∈ R, (S.filter fun f ↦ π f = J).card) ≤
        ∑ _J ∈ R,
          (Nat.choose (n - j) (r - 1 - j) * D) := by
      apply Finset.sum_le_sum
      intro J hJ
      have hJdata := Finset.mem_powersetCard.mp hJ
      have hsub : (S.filter fun f ↦ π f = J) ⊆
          K.filter fun f ↦ J ⊆ f := by
        intro f hf
        have hfdata := Finset.mem_filter.mp hf
        have hfS := Finset.mem_filter.mp hfdata.1
        apply Finset.mem_filter.mpr
        refine ⟨hfS.1, ?_⟩
        rw [← hfdata.2]
        exact Finset.inter_subset_right
      exact (Finset.card_le_card hsub).trans
        (localDegree_le_choose_mul_of_codimOneDegree hr hK hdeg
          hJdata.2 hj)
    _ = Nat.choose r j *
        (Nat.choose (n - j) (r - 1 - j) * D) := by
      simp [R, hecard]

/-- In a uniform family with codimension-one degree at most `D`, ordered
edge pairs whose intersection has any fixed positive size below `r` have
the required one-power saving. -/
theorem card_orderedIntersectionPairs_le_of_codimOneDegree
    {r j D : ℕ} (hr : 0 < r) {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    (hdeg : ∀ I : Finset (Fin n), I.card = r - 1 →
      (K.filter fun e ↦ I ⊆ e).card ≤ D)
    (hj : j < r) :
    (orderedIntersectionPairs K j).card ≤
      K.card *
        (Nat.choose r j *
          (Nat.choose (n - j) (r - 1 - j) * D)) := by
  classical
  let P := orderedIntersectionPairs K j
  have hmaps : (P : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
      Prod.fst K := by
    intro p hp
    exact (mem_orderedIntersectionPairs.mp hp).1
  rw [show (orderedIntersectionPairs K j).card = P.card by rfl,
    Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    (∑ e ∈ K, (P.filter fun p ↦ p.1 = e).card) ≤
        ∑ _e ∈ K,
          (Nat.choose r j *
            (Nat.choose (n - j) (r - 1 - j) * D)) := by
      apply Finset.sum_le_sum
      intro e he
      have hsubcard : (P.filter fun p ↦ p.1 = e).card =
          (K.filter fun f ↦ (e ∩ f).card = j).card := by
        apply Finset.card_bij
          (s := P.filter fun p ↦ p.1 = e)
          (t := K.filter fun f ↦ (e ∩ f).card = j)
          (fun p _hp ↦ p.2)
        · intro p hp
          have hpdata := Finset.mem_filter.mp hp
          have hpair := mem_orderedIntersectionPairs.mp hpdata.1
          exact Finset.mem_filter.mpr
            ⟨hpair.2.1, by simpa [hpdata.2] using hpair.2.2⟩
        · intro p hp q hq hpq
          have hp₁ := (Finset.mem_filter.mp hp).2
          have hq₁ := (Finset.mem_filter.mp hq).2
          exact Prod.ext (hp₁.trans hq₁.symm) hpq
        · intro f hf
          have hfdata := Finset.mem_filter.mp hf
          refine ⟨(e, f), ?_, rfl⟩
          exact Finset.mem_filter.mpr
            ⟨mem_orderedIntersectionPairs.mpr
              ⟨he, hfdata.1, hfdata.2⟩, rfl⟩
      rw [hsubcard]
      exact card_intersection_filter_le_of_codimOneDegree hr hK hdeg
        (hK e he) hj
    _ = K.card *
        (Nat.choose r j *
          (Nat.choose (n - j) (r - 1 - j) * D)) := by simp

/-! ## Independent colour-indexed rotations -/

/-- The sample space for `m` independent uniformly counted vertex
permutations. -/
def rotationSamples (n m : ℕ) :
    Finset (Fin m → Equiv.Perm (Fin n)) :=
  Finset.univ

@[simp] lemma card_rotationSamples (n m : ℕ) :
    (rotationSamples n m).card =
      Fintype.card (Equiv.Perm (Fin n)) ^ m := by
  simp [rotationSamples, Fintype.card_fun]

/-- Samples for which every colour-indexed target edge lands in the
corresponding independent rotation of `K`. -/
def rainbowHitSamples {n m : ℕ} (K : Finset (Finset (Fin n)))
    (targets : Fin m → Finset (Fin n)) :
    Finset (Fin m → Equiv.Perm (Fin n)) :=
  Fintype.piFinset fun i ↦ hitPermutations K (targets i)

@[simp] lemma mem_rainbowHitSamples
    {n m : ℕ} {K : Finset (Finset (Fin n))}
    {targets : Fin m → Finset (Fin n)}
    {σ : Fin m → Equiv.Perm (Fin n)} :
    σ ∈ rainbowHitSamples K targets ↔
      ∀ i, rotateEdge (σ i).symm (targets i) ∈ K := by
  simp [rainbowHitSamples]

@[simp] lemma card_rainbowHitSamples
    {n m : ℕ} (K : Finset (Finset (Fin n)))
    (targets : Fin m → Finset (Fin n)) :
    (rainbowHitSamples K targets).card =
      ∏ i, (hitPermutations K (targets i)).card := by
  simp [rainbowHitSamples]

lemma hitPermutations_inter (K : Finset (Finset (Fin n)))
    (target₁ target₂ : Finset (Fin n)) :
    hitPermutations K target₁ ∩ hitPermutations K target₂ =
      pairHitPermutations K target₁ target₂ := by
  ext σ
  simp

/-- Intersecting two rainbow-hit events is coordinatewise the two-edge
hit event. -/
lemma rainbowHitSamples_inter
    {n m : ℕ} (K : Finset (Finset (Fin n)))
    (targets₁ targets₂ : Fin m → Finset (Fin n)) :
    rainbowHitSamples K targets₁ ∩ rainbowHitSamples K targets₂ =
      Fintype.piFinset fun i ↦
        pairHitPermutations K (targets₁ i) (targets₂ i) := by
  rw [rainbowHitSamples, rainbowHitSamples,
    ← Fintype.piFinset_inter]
  congr 1
  funext i
  exact hitPermutations_inter K (targets₁ i) (targets₂ i)

/-- Exact product law for the probability that all colour-indexed target
edges hit one uniform family.  Denominators are cleared, so the identity
is entirely in `ℕ`. -/
theorem card_rainbowHitSamples_mul_choose_pow
    {n m r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {targets : Fin m → Finset (Fin n)}
    (htargets : ∀ i, (targets i).card = r) :
    (rainbowHitSamples K targets).card * Nat.choose n r ^ m =
      K.card ^ m * Fintype.card (Equiv.Perm (Fin n)) ^ m := by
  classical
  calc
    (rainbowHitSamples K targets).card * Nat.choose n r ^ m =
        (∏ i, (hitPermutations K (targets i)).card) *
          (∏ _i : Fin m, Nat.choose n r) := by simp
    _ = ∏ i, ((hitPermutations K (targets i)).card *
          Nat.choose n r) := by rw [Finset.prod_mul_distrib]
    _ = ∏ _i : Fin m,
          (K.card * Fintype.card (Equiv.Perm (Fin n))) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact card_hitPermutations_mul_choose hK (htargets i)
    _ = K.card ^ m * Fintype.card (Equiv.Perm (Fin n)) ^ m := by
      rw [← mul_pow]
      simp

/-- Exact product law for the intersection of two rainbow-hit events.
Each colour may have a different target intersection size. -/
theorem card_rainbowHitSamples_inter_mul_uniformPairProduct
    {n m r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {targets₁ targets₂ : Fin m → Finset (Fin n)}
    (htargets₁ : ∀ i, (targets₁ i).card = r)
    (htargets₂ : ∀ i, (targets₂ i).card = r) :
    (rainbowHitSamples K targets₁ ∩
        rainbowHitSamples K targets₂).card *
        (∏ i, (orderedIntersectionPairs
          (Erdos722.Typicality.uniformEdges n r)
          ((targets₁ i ∩ targets₂ i).card)).card) =
      (∏ i, (orderedIntersectionPairs K
          ((targets₁ i ∩ targets₂ i).card)).card) *
        Fintype.card (Equiv.Perm (Fin n)) ^ m := by
  classical
  rw [rainbowHitSamples_inter, Fintype.card_piFinset]
  calc
    (∏ i, (pairHitPermutations K
          (targets₁ i) (targets₂ i)).card) *
        (∏ i, (orderedIntersectionPairs
          (Erdos722.Typicality.uniformEdges n r)
          ((targets₁ i ∩ targets₂ i).card)).card) =
        ∏ i, ((pairHitPermutations K
            (targets₁ i) (targets₂ i)).card *
          (orderedIntersectionPairs
            (Erdos722.Typicality.uniformEdges n r)
            ((targets₁ i ∩ targets₂ i).card)).card) := by
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ((orderedIntersectionPairs K
          ((targets₁ i ∩ targets₂ i).card)).card *
        Fintype.card (Equiv.Perm (Fin n))) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact card_pairHitPermutations_mul_uniformIntersectionPairs hK
        (htargets₁ i) (htargets₂ i)
    _ = (∏ i, (orderedIntersectionPairs K
          ((targets₁ i ∩ targets₂ i).card)).card) *
        Fintype.card (Equiv.Perm (Fin n)) ^ m := by
      rw [Finset.prod_mul_distrib]
      simp

/-- A coordinatewise correlation ratio tensorizes across independent
colour rotations. -/
theorem card_rainbowHitSamples_inter_ratio_of_coordinate
    {n m c : ℕ} (K : Finset (Finset (Fin n)))
    (targets₁ targets₂ : Fin m → Finset (Fin n))
    (hcoord : ∀ i,
      Fintype.card (Equiv.Perm (Fin n)) *
          (pairHitPermutations K (targets₁ i) (targets₂ i)).card ≤
        c * (hitPermutations K (targets₁ i)).card *
          (hitPermutations K (targets₂ i)).card) :
    Fintype.card (Fin m → Equiv.Perm (Fin n)) *
        (rainbowHitSamples K targets₁ ∩
          rainbowHitSamples K targets₂).card ≤
      c ^ m * (rainbowHitSamples K targets₁).card *
        (rainbowHitSamples K targets₂).card := by
  classical
  rw [Fintype.card_fun, rainbowHitSamples_inter,
    Fintype.card_piFinset, card_rainbowHitSamples,
    card_rainbowHitSamples]
  simp only [Fintype.card_fin]
  calc
    Fintype.card (Equiv.Perm (Fin n)) ^ m *
          (∏ i, (pairHitPermutations K
            (targets₁ i) (targets₂ i)).card) =
        ∏ i, (Fintype.card (Equiv.Perm (Fin n)) *
          (pairHitPermutations K
            (targets₁ i) (targets₂ i)).card) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ ∏ i, (c * (hitPermutations K (targets₁ i)).card *
          (hitPermutations K (targets₂ i)).card) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hcoord i
    _ = c ^ m * (∏ i, (hitPermutations K (targets₁ i)).card) *
        ∏ i, (hitPermutations K (targets₂ i)).card := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      simp [mul_assoc]

/-- An ordered-intersection-pair density bound for the base family implies
the corresponding one-coordinate permutation correlation bound.  All
denominators are cleared, and positivity follows from the displayed target
pair itself. -/
theorem card_pairHitPermutations_ratio_of_orderedPair_ratio
    {n r c : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {target₁ target₂ : Finset (Fin n)}
    (htarget₁ : target₁.card = r)
    (htarget₂ : target₂.card = r)
    (hratio :
      (orderedIntersectionPairs K
          ((target₁ ∩ target₂).card)).card *
          Nat.choose n r ^ 2 ≤
        c * K.card ^ 2 *
          (orderedIntersectionPairs
            (Erdos722.Typicality.uniformEdges n r)
            ((target₁ ∩ target₂).card)).card) :
    Fintype.card (Equiv.Perm (Fin n)) *
        (pairHitPermutations K target₁ target₂).card ≤
      c * (hitPermutations K target₁).card *
        (hitPermutations K target₂).card := by
  classical
  let U := Nat.choose n r
  let S := Fintype.card (Equiv.Perm (Fin n))
  let P := (orderedIntersectionPairs
    (Erdos722.Typicality.uniformEdges n r)
    ((target₁ ∩ target₂).card)).card
  let PK := (orderedIntersectionPairs K
    ((target₁ ∩ target₂).card)).card
  let H₁ := (hitPermutations K target₁).card
  let H₂ := (hitPermutations K target₂).card
  let B := (pairHitPermutations K target₁ target₂).card
  have hUpos : 0 < U := by
    apply Nat.choose_pos
    calc
      r = target₁.card := htarget₁.symm
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ target₁)
      _ = n := by simp
  have hPpos : 0 < P := by
    apply Finset.card_pos.mpr
    refine ⟨(target₁, target₂), ?_⟩
    exact mem_orderedIntersectionPairs.mpr
      ⟨Erdos722.Typicality.mem_uniformEdges.mpr htarget₁,
        Erdos722.Typicality.mem_uniformEdges.mpr htarget₂, rfl⟩
  have hH₁ : H₁ * U = K.card * S := by
    simpa [H₁, U, S] using
      card_hitPermutations_mul_choose hK htarget₁
  have hH₂ : H₂ * U = K.card * S := by
    simpa [H₂, U, S] using
      card_hitPermutations_mul_choose hK htarget₂
  have hB : B * P = PK * S := by
    simpa [B, P, PK, S] using
      card_pairHitPermutations_mul_uniformIntersectionPairs
        hK htarget₁ htarget₂
  have hscaled :
      (S * B) * (P * U ^ 2) ≤
        (c * H₁ * H₂) * (P * U ^ 2) := by
    calc
      (S * B) * (P * U ^ 2) = S * (B * P) * U ^ 2 := by ring
      _ = S * (PK * S) * U ^ 2 := by rw [hB]
      _ = S ^ 2 * (PK * U ^ 2) := by ring
      _ ≤ S ^ 2 * (c * K.card ^ 2 * P) := by
        apply Nat.mul_le_mul_left
        simpa [PK, P, U] using hratio
      _ = c * (K.card * S) * (K.card * S) * P := by ring
      _ = c * (H₁ * U) * (H₂ * U) * P := by
        rw [hH₁, hH₂]
      _ = (c * H₁ * H₂) * (P * U ^ 2) := by ring
  have hden : 0 < P * U ^ 2 := mul_pos hPpos (pow_pos hUpos _)
  exact Nat.le_of_mul_le_mul_right (c := P * U ^ 2) hscaled hden

/-! ## Rooted candidate-pair geometry -/

/-- Two rooted embeddings are in general position when their images away
from the prescribed root are disjoint. -/
def RootedOutsideDisjoint {v n : ℕ} (root : Finset (Fin v))
    (φ ψ : Fin v ↪ Fin n) : Prop :=
  Disjoint
    (Erdos722.RootedEmbedding.mapEdge φ
      (Erdos722.RootedEmbedding.outsideRoot root))
    (Erdos722.RootedEmbedding.mapEdge ψ
      (Erdos722.RootedEmbedding.outsideRoot root))

/-- Exceptional partners of one rooted embedding. -/
noncomputable def rootedExceptionalPartners
    {v n : ℕ} (root : Finset (Fin v))
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    (φ : Fin v ↪ Fin n) : Finset (Fin v ↪ Fin n) := by
  classical
  exact (Erdos722.RootedEmbedding.rootedEmbeddings root request).filter
    fun ψ ↦ ¬RootedOutsideDisjoint root φ ψ

/-- For a fixed rooted embedding, the embeddings not in general position
lose one ground-set power. -/
theorem card_rootedExceptionalPartners_le
    {v n : ℕ} (root : Finset (Fin v))
    (request : Erdos722.RootedEmbedding.RootRequest v n root)
    (φ : Fin v ↪ Fin n) :
    (rootedExceptionalPartners root request φ).card ≤
      (v - root.card) ^ 2 * n ^ (v - (root.card + 1)) := by
  classical
  let J := Erdos722.RootedEmbedding.mapEdge φ
    (Erdos722.RootedEmbedding.outsideRoot root)
  have hsub :
      rootedExceptionalPartners root request φ ⊆
        (Erdos722.RootedEmbedding.rootedEmbeddings root request).filter
          (fun ψ ↦ Erdos722.RootedEmbedding.outsideRootTouchHit
            root J [] ψ) := by
    intro ψ hψ
    change ψ ∈
      (Erdos722.RootedEmbedding.rootedEmbeddings root request).filter
        (fun ψ ↦ ¬RootedOutsideDisjoint root φ ψ) at hψ
    have hψdata := Finset.mem_filter.mp hψ
    apply Finset.mem_filter.mpr
    refine ⟨hψdata.1, ?_⟩
    apply (Erdos722.RootedEmbedding.outsideRootTouchHit_eq_true_iff
      root J [] ψ).mpr
    rw [RootedOutsideDisjoint, Finset.not_disjoint_iff] at hψdata
    obtain ⟨y, hyφ, hyψ⟩ := hψdata.2
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hyψ
    refine ⟨x, hx, ?_⟩
    rw [hxy]
    exact hyφ
  calc
    (rootedExceptionalPartners root request φ).card ≤
        ((Erdos722.RootedEmbedding.rootedEmbeddings root request).filter
          (fun ψ ↦ Erdos722.RootedEmbedding.outsideRootTouchHit
            root J [] ψ)).card := Finset.card_le_card hsub
    _ ≤ (v - root.card) * J.card *
        n ^ (v - (root.card + 1)) :=
      Erdos722.RootedEmbedding.card_rootedEmbeddings_outsideRootTouches_le
        root request J
    _ = (v - root.card) ^ 2 *
        n ^ (v - (root.card + 1)) := by
      simp [J, pow_two]

/-- In general position, two copies of the same pattern set intersect
exactly in its prescribed root part. -/
theorem mapEdge_inter_mapEdge_eq_rootPart
    {v n : ℕ} {root S : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {φ ψ : Fin v ↪ Fin n}
    (hφ : Erdos722.RootedEmbedding.ExtendsRequest root request φ)
    (hψ : Erdos722.RootedEmbedding.ExtendsRequest root request ψ)
    (hdisj : RootedOutsideDisjoint root φ ψ) :
    Erdos722.RootedEmbedding.mapEdge φ S ∩
        Erdos722.RootedEmbedding.mapEdge ψ S =
      Erdos722.RootedEmbedding.mapEdge φ (S ∩ root) := by
  classical
  ext y
  constructor
  · intro hy
    have hydata := Finset.mem_inter.mp hy
    obtain ⟨x, hxS, hxy⟩ := Finset.mem_map.mp hydata.1
    obtain ⟨z, hzS, hzy⟩ := Finset.mem_map.mp hydata.2
    have hxroot : x ∈ root := by
      by_contra hxroot
      by_cases hzroot : z ∈ root
      · have hφzψz : φ z = ψ z := (hφ z hzroot).trans (hψ z hzroot).symm
        have hφxφz : φ x = φ z := hxy.trans (hzy.symm.trans hφzψz.symm)
        have hxz : x = z := φ.injective hφxφz
        exact hxroot (hxz ▸ hzroot)
      · have hxOutside : x ∈ Erdos722.RootedEmbedding.outsideRoot root :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxroot⟩
        have hzOutside : z ∈ Erdos722.RootedEmbedding.outsideRoot root :=
          Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzroot⟩
        apply Finset.disjoint_left.mp hdisj
        · exact Finset.mem_map.mpr ⟨x, hxOutside, hxy⟩
        · exact Finset.mem_map.mpr ⟨z, hzOutside, hzy⟩
    exact Finset.mem_map.mpr
      ⟨x, Finset.mem_inter.mpr ⟨hxS, hxroot⟩, hxy⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    have hxdata := Finset.mem_inter.mp hx
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_map.mpr ⟨x, hxdata.1, hxy⟩
    · apply Finset.mem_map.mpr
      refine ⟨x, hxdata.1, ?_⟩
      exact (hψ x hxdata.2).trans ((hφ x hxdata.2).symm.trans hxy)

lemma card_mapEdge_inter_mapEdge_of_rootedOutsideDisjoint
    {v n : ℕ} {root S : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {φ ψ : Fin v ↪ Fin n}
    (hφ : Erdos722.RootedEmbedding.ExtendsRequest root request φ)
    (hψ : Erdos722.RootedEmbedding.ExtendsRequest root request ψ)
    (hdisj : RootedOutsideDisjoint root φ ψ) :
    (Erdos722.RootedEmbedding.mapEdge φ S ∩
      Erdos722.RootedEmbedding.mapEdge ψ S).card = (S ∩ root).card := by
  rw [mapEdge_inter_mapEdge_eq_rootPart hφ hψ hdisj]
  exact Erdos722.RootedEmbedding.card_mapEdge φ (S ∩ root)

/-! ## Rooted rotation events -/

/-- The colour-indexed ground edges obtained from a rooted embedding of a
fixed colour-indexed pattern family. -/
def mappedTargets {v n m : ℕ}
    (edges : Fin m → Finset (Fin v)) (φ : Fin v ↪ Fin n) :
    Fin m → Finset (Fin n) :=
  fun i ↦ Erdos722.RootedEmbedding.mapEdge φ (edges i)

/-- The rotation event that every mapped pattern edge lands in its
independently coloured copy of `K`. -/
def rootedRotationSuccess {v n m : ℕ}
    (K : Finset (Finset (Fin n)))
    (edges : Fin m → Finset (Fin v)) (φ : Fin v ↪ Fin n) :
    Finset (Fin m → Equiv.Perm (Fin n)) :=
  rainbowHitSamples K (mappedTargets edges φ)

@[simp] lemma mem_rootedRotationSuccess
    {v n m : ℕ} {K : Finset (Finset (Fin n))}
    {edges : Fin m → Finset (Fin v)} {φ : Fin v ↪ Fin n}
    {σ : Fin m → Equiv.Perm (Fin n)} :
    σ ∈ rootedRotationSuccess K edges φ ↔
      ∀ i, rotateEdge (σ i).symm
        (Erdos722.RootedEmbedding.mapEdge φ (edges i)) ∈ K := by
  simp [rootedRotationSuccess, mappedTargets]

/-- One-edge hit-event cardinality depends only on the target cardinality. -/
lemma card_hitPermutations_eq_of_target_card_eq
    {n r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {target₁ target₂ : Finset (Fin n)}
    (htarget₁ : target₁.card = r) (htarget₂ : target₂.card = r) :
    (hitPermutations K target₁).card =
      (hitPermutations K target₂).card := by
  have h₁ := card_hitPermutations_mul_choose hK htarget₁
  have h₂ := card_hitPermutations_mul_choose hK htarget₂
  have hrn : r ≤ n := by
    calc
      r = target₁.card := htarget₁.symm
      _ ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ target₁)
      _ = n := by simp
  have hchoose : 0 < Nat.choose n r := Nat.choose_pos hrn
  exact Nat.eq_of_mul_eq_mul_right hchoose (h₁.trans h₂.symm)

/-- Hence a colour-product hit-event cardinality is independent of the
particular embedding whenever all pattern constraints have the same fixed
cardinality. -/
lemma card_rootedRotationSuccess_eq
    {v n m r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    (φ ψ : Fin v ↪ Fin n) :
    (rootedRotationSuccess K edges φ).card =
      (rootedRotationSuccess K edges ψ).card := by
  simp only [rootedRotationSuccess, card_rainbowHitSamples]
  apply Finset.prod_congr rfl
  intro i _hi
  apply card_hitPermutations_eq_of_target_card_eq hK
  · simpa [mappedTargets] using
      Erdos722.RootedEmbedding.card_mapEdge φ (edges i)
        |>.trans (hedges i)
  · simpa [mappedTargets] using
      Erdos722.RootedEmbedding.card_mapEdge ψ (edges i)
        |>.trans (hedges i)

/-- Two-edge hit-event cardinality depends only on the two target
cardinalities and their intersection cardinality. -/
lemma card_pairHitPermutations_eq_of_inter_card_eq
    {n r : ℕ} {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {a₁ a₂ b₁ b₂ : Finset (Fin n)}
    (ha₁ : a₁.card = r) (ha₂ : a₂.card = r)
    (hb₁ : b₁.card = r) (hb₂ : b₂.card = r)
    (hinter : (a₁ ∩ a₂).card = (b₁ ∩ b₂).card) :
    (pairHitPermutations K a₁ a₂).card =
      (pairHitPermutations K b₁ b₂).card := by
  let j := (a₁ ∩ a₂).card
  have h₁ := card_pairHitPermutations_mul_uniformIntersectionPairs
    hK ha₁ ha₂
  have h₂ := card_pairHitPermutations_mul_uniformIntersectionPairs
    hK hb₁ hb₂
  rw [← hinter] at h₂
  let U := orderedIntersectionPairs
    (Erdos722.Typicality.uniformEdges n r) j
  have hpair : (a₁, a₂) ∈ U := by
    apply mem_orderedIntersectionPairs.mpr
    exact ⟨Erdos722.Typicality.mem_uniformEdges.mpr ha₁,
      Erdos722.Typicality.mem_uniformEdges.mpr ha₂, rfl⟩
  have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨(a₁, a₂), hpair⟩
  exact Nat.eq_of_mul_eq_mul_right hUpos (h₁.trans h₂.symm)

/-- For rooted embeddings in general position, the intersection of their
two rotation-success events has one fixed cardinality. -/
lemma card_rootedRotationSuccess_inter_eq_of_outsideDisjoint
    {v n m r : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ ψ φ' ψ' : Fin v ↪ Fin n}
    (hφ : Erdos722.RootedEmbedding.ExtendsRequest root request φ)
    (hψ : Erdos722.RootedEmbedding.ExtendsRequest root request ψ)
    (hφ' : Erdos722.RootedEmbedding.ExtendsRequest root request φ')
    (hψ' : Erdos722.RootedEmbedding.ExtendsRequest root request ψ')
    (hdisj : RootedOutsideDisjoint root φ ψ)
    (hdisj' : RootedOutsideDisjoint root φ' ψ') :
    (rootedRotationSuccess K edges φ ∩
        rootedRotationSuccess K edges ψ).card =
      (rootedRotationSuccess K edges φ' ∩
        rootedRotationSuccess K edges ψ').card := by
  rw [rootedRotationSuccess, rootedRotationSuccess,
    rootedRotationSuccess, rootedRotationSuccess,
    rainbowHitSamples_inter, rainbowHitSamples_inter,
    Fintype.card_piFinset, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i _hi
  apply card_pairHitPermutations_eq_of_inter_card_eq hK
  · exact (Erdos722.RootedEmbedding.card_mapEdge φ (edges i)).trans
      (hedges i)
  · exact (Erdos722.RootedEmbedding.card_mapEdge ψ (edges i)).trans
      (hedges i)
  · exact (Erdos722.RootedEmbedding.card_mapEdge φ' (edges i)).trans
      (hedges i)
  · exact (Erdos722.RootedEmbedding.card_mapEdge ψ' (edges i)).trans
      (hedges i)
  · change (Erdos722.RootedEmbedding.mapEdge φ (edges i) ∩
        Erdos722.RootedEmbedding.mapEdge ψ (edges i)).card =
      (Erdos722.RootedEmbedding.mapEdge φ' (edges i) ∩
        Erdos722.RootedEmbedding.mapEdge ψ' (edges i)).card
    rw [card_mapEdge_inter_mapEdge_of_rootedOutsideDisjoint
        hφ hψ hdisj,
      card_mapEdge_inter_mapEdge_of_rootedOutsideDisjoint
        hφ' hψ' hdisj']

/-- Rooted rotation covering, in the exact finite second-moment form used
by all four applications of Lemma 6.3.  All pattern geometry is discharged
here; an application only has to verify the displayed scalar variance
inequality. -/
theorem card_rootedRotationFailures_le
    {v n m r B : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hvariance :
      let candidates :=
        Erdos722.RootedEmbedding.rootedEmbeddings root request
      let A := (rootedRotationSuccess K edges φ₀).card
      let G := (rootedRotationSuccess K edges φ₀ ∩
        rootedRotationSuccess K edges φ₁).card
      let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
      (Fintype.card (Fin m → Equiv.Perm (Fin n)) : ℤ) ^ 2 *
          ((candidates.card ^ 2 * G + candidates.card * L * A : ℕ) : ℤ) -
        (Fintype.card (Fin m → Equiv.Perm (Fin n)) : ℤ) *
          ((candidates.card * A : ℕ) : ℤ) ^ 2 ≤
        (B : ℤ) * ((candidates.card * A : ℕ) : ℤ) ^ 2) :
    ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ = 0).card ≤ B := by
  classical
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let success := rootedRotationSuccess K edges
  let good : (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Prop :=
    fun φ ψ ↦ RootedOutsideDisjoint root φ ψ
  let A := (success φ₀).card
  let G := (success φ₀ ∩ success φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  have hφ₀mem : φ₀ ∈ candidates := by
    exact Erdos722.RootedEmbedding.mem_rootedEmbeddings.mpr hφ₀
  have hcandidates : 0 < candidates.card :=
    Finset.card_pos.mpr ⟨φ₀, hφ₀mem⟩
  have hcard : ∀ φ ∈ candidates, (success φ).card = A := by
    intro φ hφ
    exact card_rootedRotationSuccess_eq hK hedges φ φ₀
  have hgood : ∀ φ ∈ candidates, ∀ ψ ∈ candidates, good φ ψ →
      (success φ ∩ success ψ).card ≤ G := by
    intro φ hφ ψ hψ hφψ
    have hextφ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ
    have hextψ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hψ
    exact Nat.le_of_eq
      (card_rootedRotationSuccess_inter_eq_of_outsideDisjoint
        hK hedges hextφ hextψ hφ₀ hφ₁ hφψ hdisj)
  have hexceptional : ∀ φ ∈ candidates,
      (candidates.filter fun ψ ↦ ¬good φ ψ).card ≤ L := by
    intro φ hφ
    simpa [candidates, good, L, rootedExceptionalPartners] using
      card_rootedExceptionalPartners_le root request φ
  have hbound :=
    Erdos722.Probability.card_samples_with_no_success_le_of_pair_bounds
      candidates success good A G L B hcandidates hApos hcard hgood
        hexceptional (by
          simpa [candidates, success, A, G, L] using hvariance)
  simpa [rotationSamples, candidates, success] using hbound

/-- Scaled counterpart of `card_rootedRotationFailures_le`.  A constant
second-moment ratio is enough here: the later colour-group amplification
uses `D * |bad| ≤ E * |Sample|` directly and never divides natural
cardinalities. -/
theorem card_rootedRotationFailures_scaled
    {v n m r D E : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hscale :
      let candidates :=
        Erdos722.RootedEmbedding.rootedEmbeddings root request
      let A := (rootedRotationSuccess K edges φ₀).card
      let G := (rootedRotationSuccess K edges φ₀ ∩
        rootedRotationSuccess K edges φ₁).card
      let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
      D * Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        E * (candidates.card * A) ^ 2) :
    D * ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ = 0).card ≤
      E * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  classical
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let success := rootedRotationSuccess K edges
  let good : (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Prop :=
    fun φ ψ ↦ RootedOutsideDisjoint root φ ψ
  let A := (success φ₀).card
  let G := (success φ₀ ∩ success φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  have hφ₀mem : φ₀ ∈ candidates :=
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mpr hφ₀
  have hcandidates : 0 < candidates.card :=
    Finset.card_pos.mpr ⟨φ₀, hφ₀mem⟩
  have hcard : ∀ φ ∈ candidates, (success φ).card = A := by
    intro φ hφ
    exact card_rootedRotationSuccess_eq hK hedges φ φ₀
  have hgood : ∀ φ ∈ candidates, ∀ ψ ∈ candidates, good φ ψ →
      (success φ ∩ success ψ).card ≤ G := by
    intro φ hφ ψ hψ hφψ
    have hextφ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ
    have hextψ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hψ
    exact Nat.le_of_eq
      (card_rootedRotationSuccess_inter_eq_of_outsideDisjoint
        hK hedges hextφ hextψ hφ₀ hφ₁ hφψ hdisj)
  have hexceptional : ∀ φ ∈ candidates,
      (candidates.filter fun ψ ↦ ¬good φ ψ).card ≤ L := by
    intro φ hφ
    simpa [candidates, good, L, rootedExceptionalPartners] using
      card_rootedExceptionalPartners_le root request φ
  have hbound :=
    Erdos722.Probability.card_samples_with_no_success_scaled_of_pair_bounds
      candidates success good A G L D E hcandidates hApos hcard hgood
        hexceptional (by
          simpa [candidates, success, A, G, L] using hscale)
  simpa [rotationSamples, candidates, success] using hbound

/-- Paley--Zygmund form of rooted rotation covering.  The conclusion says
that a `1/R` fraction of all colour-rotation samples succeeds, which is the
form used by constant-factor correlation estimates and finite
amplification. -/
theorem card_rootedRotationFailures_paley_scaled
    {v n m r R : ℕ} {root : Finset (Fin v)}
    {request : Erdos722.RootedEmbedding.RootRequest v n root}
    {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r)
    {edges : Fin m → Finset (Fin v)}
    (hedges : ∀ i, (edges i).card = r)
    {φ₀ φ₁ : Fin v ↪ Fin n}
    (hφ₀ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₀)
    (hφ₁ : Erdos722.RootedEmbedding.ExtendsRequest root request φ₁)
    (hdisj : RootedOutsideDisjoint root φ₀ φ₁)
    (hApos : 0 < (rootedRotationSuccess K edges φ₀).card)
    (hR : 0 < R)
    (hratio :
      let candidates :=
        Erdos722.RootedEmbedding.rootedEmbeddings root request
      let A := (rootedRotationSuccess K edges φ₀).card
      let G := (rootedRotationSuccess K edges φ₀ ∩
        rootedRotationSuccess K edges φ₁).card
      let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          (candidates.card ^ 2 * G + candidates.card * L * A) ≤
        R * (candidates.card * A) ^ 2) :
    R * ((rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ = 0).card ≤
      (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  classical
  let candidates := Erdos722.RootedEmbedding.rootedEmbeddings root request
  let success := rootedRotationSuccess K edges
  let good : (Fin v ↪ Fin n) → (Fin v ↪ Fin n) → Prop :=
    fun φ ψ ↦ RootedOutsideDisjoint root φ ψ
  let A := (success φ₀).card
  let G := (success φ₀ ∩ success φ₁).card
  let L := (v - root.card) ^ 2 * n ^ (v - (root.card + 1))
  have hφ₀mem : φ₀ ∈ candidates :=
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mpr hφ₀
  have hcandidates : 0 < candidates.card :=
    Finset.card_pos.mpr ⟨φ₀, hφ₀mem⟩
  have hcard : ∀ φ ∈ candidates, (success φ).card = A := by
    intro φ hφ
    exact card_rootedRotationSuccess_eq hK hedges φ φ₀
  have hgood : ∀ φ ∈ candidates, ∀ ψ ∈ candidates, good φ ψ →
      (success φ ∩ success ψ).card ≤ G := by
    intro φ hφ ψ hψ hφψ
    have hextφ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφ
    have hextψ := Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hψ
    exact Nat.le_of_eq
      (card_rootedRotationSuccess_inter_eq_of_outsideDisjoint
        hK hedges hextφ hextψ hφ₀ hφ₁ hφψ hdisj)
  have hexceptional : ∀ φ ∈ candidates,
      (candidates.filter fun ψ ↦ ¬good φ ψ).card ≤ L := by
    intro φ hφ
    simpa [candidates, good, L, rootedExceptionalPartners] using
      card_rootedExceptionalPartners_le root request φ
  have hbound :=
    Erdos722.Probability.card_samples_with_no_success_paley_scaled_of_pair_bounds
      candidates success good A G L R hR hcandidates hApos hcard hgood
        hexceptional (by
          simpa [candidates, success, A, G, L] using hratio)
  simpa [rotationSamples, candidates, success] using hbound

/-- Amplify a uniform scaled failure bound over every root request and
extract an actual successful rooted embedding.  A successful colour group
is returned together with the embedding and the coordinatewise membership
conditions, ready for deterministic pattern-specific decoding. -/
theorem exists_amplified_rootedRotationCover_of_scaled_bad
    {v n m r R g : ℕ} {root : Finset (Fin v)}
    (K : Finset (Finset (Fin n)))
    (edges : Fin m → Finset (Fin v))
    (hR : 0 < R)
    (hbad : ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
      R * ((rotationSamples n m).filter fun σ ↦
        Erdos722.Probability.finiteSuccessCount
          (Erdos722.RootedEmbedding.rootedEmbeddings root request)
          (rootedRotationSuccess K edges) σ = 0).card ≤
        (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)))
    (hunion :
      Nat.card (Erdos722.RootedEmbedding.RootRequest v n root) *
          (R - 1) ^ g < R ^ g) :
    ∃ choice : Fin g → (Fin m → Equiv.Perm (Fin n)),
      ∀ request : Erdos722.RootedEmbedding.RootRequest v n root,
        ∃ t : Fin g, ∃ φ : Fin v ↪ Fin n,
          Erdos722.RootedEmbedding.ExtendsRequest root request φ ∧
          ∀ i, rotateEdge (choice t i).symm
            (Erdos722.RootedEmbedding.mapEdge φ (edges i)) ∈ K := by
  classical
  let Task := Erdos722.RootedEmbedding.RootRequest v n root
  let Sample := Fin m → Equiv.Perm (Fin n)
  letI : Fintype Task := Fintype.ofInjective
    Erdos722.RootedEmbedding.RootRequest.map (by
      intro a b hab
      cases a with
      | mk amap ainj =>
        cases b with
        | mk bmap binj =>
          simp only [Erdos722.RootedEmbedding.RootRequest.map] at hab
          cases hab
          rfl)
  let tasks : Finset Task := Finset.univ
  let bad : Task → Finset Sample := fun request ↦
    (rotationSamples n m).filter fun σ ↦
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) σ = 0
  have hbad' : ∀ request ∈ tasks,
      R * (bad request).card ≤
        (R - 1) * Fintype.card Sample := by
    intro request hrequest
    simpa [bad, Sample] using hbad request
  obtain ⟨choice, hchoice⟩ :=
    Erdos722.Probability.exists_amplified_cover_of_scaled_bad
      tasks bad R (R - 1) g hR hbad' (by
        simpa [tasks, Task] using hunion)
  refine ⟨choice, ?_⟩
  intro request
  obtain ⟨t, ht⟩ := hchoice request (Finset.mem_univ _)
  have hnonzero :
      Erdos722.Probability.finiteSuccessCount
        (Erdos722.RootedEmbedding.rootedEmbeddings root request)
        (rootedRotationSuccess K edges) (choice t) ≠ 0 := by
    intro hzero
    apply ht
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hzero⟩
  have hpositive := Nat.pos_of_ne_zero hnonzero
  change 0 <
      ((Erdos722.RootedEmbedding.rootedEmbeddings root request).filter
        fun φ ↦ choice t ∈ rootedRotationSuccess K edges φ).card at hpositive
  obtain ⟨φ, hφ⟩ := Finset.card_pos.mp hpositive
  have hφdata := Finset.mem_filter.mp hφ
  refine ⟨t, φ,
    Erdos722.RootedEmbedding.mem_rootedEmbeddings.mp hφdata.1, ?_⟩
  exact mem_rootedRotationSuccess.mp hφdata.2

lemma card_uniformEdges_containing_vertex
    {r : ℕ} (hr : 0 < r) (x : Fin n) :
    ((Erdos722.Typicality.uniformEdges n r).filter fun e ↦ x ∈ e).card =
      Nat.choose (n - 1) (r - 1) := by
  have hsingleton : ({x} : Finset (Fin n)).card ≤ r := by simp; omega
  have heq :
      ((Erdos722.Typicality.uniformEdges n r).filter fun e ↦ x ∈ e) =
        ((Finset.univ : Finset (Fin n)).powersetCard r).filter
          (fun e ↦ {x} ⊆ e) := by
    ext e
    simp [Erdos722.Typicality.uniformEdges]
  rw [heq, Finset.card_filter_powersetCard_subset {x} Finset.univ r
    (Finset.subset_univ _) hsingleton]
  simp

/-- A uniform edge meets at most `r * n^(r-1)` other uniform edges.  This
coarse form is sufficient for the overlapping-pair error in the second
moment. -/
theorem card_uniformEdges_not_disjoint_le
    {r : ℕ} (hr : 0 < r) {e : Finset (Fin n)} (hecard : e.card = r) :
    ((Erdos722.Typicality.uniformEdges n r).filter
        fun f ↦ ¬ Disjoint e f).card ≤ r * n ^ (r - 1) := by
  classical
  let U := Erdos722.Typicality.uniformEdges n r
  let meet := U.filter fun f ↦ ¬ Disjoint e f
  let through (x : Fin n) := U.filter fun f ↦ x ∈ f
  have hsub : meet ⊆ e.biUnion through := by
    intro f hf
    have hfdata := Finset.mem_filter.mp hf
    have hinter : (e ∩ f).Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      simpa [Finset.disjoint_iff_inter_eq_empty] using hfdata.2
    obtain ⟨x, hx⟩ := hinter
    apply Finset.mem_biUnion.mpr
    exact ⟨x, (Finset.mem_inter.mp hx).1,
      Finset.mem_filter.mpr ⟨hfdata.1, (Finset.mem_inter.mp hx).2⟩⟩
  have hchoose : Nat.choose (n - 1) (r - 1) ≤ n ^ (r - 1) := by
    calc
      Nat.choose (n - 1) (r - 1) ≤ (n - 1) ^ (r - 1) :=
        Nat.choose_le_pow _ _
      _ ≤ n ^ (r - 1) := Nat.pow_le_pow_left (Nat.sub_le n 1) _
  calc
    meet.card ≤ (e.biUnion through).card := Finset.card_le_card hsub
    _ ≤ ∑ x ∈ e, (through x).card := Finset.card_biUnion_le
    _ = ∑ _x ∈ e, Nat.choose (n - 1) (r - 1) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact card_uniformEdges_containing_vertex hr x
    _ ≤ ∑ _x ∈ e, n ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro x hx
      exact hchoose
    _ = r * n ^ (r - 1) := by simp [hecard]

/-- The number of non-disjoint ordered pairs inside a uniform family has
the elementary codimension-one bound needed by the rotation variance. -/
theorem card_orderedDisjointPairs_add_error
    {r : ℕ} (hr : 0 < r) {K : Finset (Finset (Fin n))}
    (hK : ∀ e ∈ K, e.card = r) :
    K.card ^ 2 ≤ (orderedDisjointPairs K).card +
      K.card * (r * n ^ (r - 1)) := by
  classical
  let all := K ×ˢ K
  let good := all.filter fun p ↦ Disjoint p.1 p.2
  let bad := all.filter fun p ↦ ¬ Disjoint p.1 p.2
  have hbad : bad.card ≤ K.card * (r * n ^ (r - 1)) := by
    have hmaps : (bad : Set (Finset (Fin n) × Finset (Fin n))).MapsTo
        Prod.fst K := by
      intro p hp
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
    have hfiber : ∀ e ∈ K,
        (bad.filter fun p ↦ p.1 = e).card =
          (K.filter fun f ↦ ¬ Disjoint e f).card := by
      intro e he
      apply Finset.card_bij
        (s := bad.filter fun p ↦ p.1 = e)
        (t := K.filter fun f ↦ ¬ Disjoint e f)
        (fun p _hp ↦ p.2)
      · intro p hp
        have hpdata := Finset.mem_filter.mp hp
        have hbadp := Finset.mem_filter.mp hpdata.1
        have hpall := Finset.mem_product.mp hbadp.1
        exact Finset.mem_filter.mpr
          ⟨hpall.2, by simpa [hpdata.2] using hbadp.2⟩
      · intro p hp q hq hpq
        have hp₁ := (Finset.mem_filter.mp hp).2
        have hq₁ := (Finset.mem_filter.mp hq).2
        exact Prod.ext (hp₁.trans hq₁.symm) hpq
      · intro f hf
        have hfdata := Finset.mem_filter.mp hf
        refine ⟨(e, f), ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨he, hfdata.1⟩, hfdata.2⟩, rfl⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    calc
      (∑ e ∈ K, ((bad.filter fun p ↦ p.1 = e).card)) =
          ∑ e ∈ K,
            ((K.filter fun f ↦ ¬ Disjoint e f).card) := by
        apply Finset.sum_congr rfl
        intro e he
        exact hfiber e he
      _ ≤ ∑ _e ∈ K, r * n ^ (r - 1) := by
        apply Finset.sum_le_sum
        intro e he
        have hsub : (K.filter fun f ↦ ¬ Disjoint e f) ⊆
            (Erdos722.Typicality.uniformEdges n r).filter
              (fun f ↦ ¬ Disjoint e f) := by
          intro f hf
          have hfdata := Finset.mem_filter.mp hf
          exact Finset.mem_filter.mpr
            ⟨Erdos722.Typicality.mem_uniformEdges.mpr (hK f hfdata.1),
              hfdata.2⟩
        exact (Finset.card_le_card hsub).trans
          (card_uniformEdges_not_disjoint_le hr (hK e he))
      _ = K.card * (r * n ^ (r - 1)) := by simp
  have hpartition : good.card + bad.card = all.card := by
    simpa [good, bad] using
      (Finset.card_filter_add_card_filter_not
        (s := all) (p := fun p ↦ Disjoint p.1 p.2))
  have hgood : good = orderedDisjointPairs K := by rfl
  have hall : all.card = K.card ^ 2 := by simp [all, pow_two]
  rw [hgood, hall] at hpartition
  omega

end

end Erdos722.Rotations
