import ErdosProblems.Erdos780.External.SignedSphere
import ErdosProblems.Erdos780.External.AllowedFaces
import Mathlib.Order.Hom.PowersetCard

namespace LabelAllowed

open ZpTuckerScratch
open SignedSphere
open AllowedFaces

noncomputable section

variable {p n m alpha : ℕ}

abbrev Vertex := NonzeroSignedVector p n
abbrev Label := ZMod p × Fin m

def labelAt (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (l : List (Vertex (p := p) (n := n))) (i : Fin l.length) :
    Label (p := p) (m := m) :=
  lab (l.get i)

def labelFace (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (l : List (Vertex (p := p) (n := n))) : Finset (Label (p := p) (m := m)) :=
  Finset.univ.image (labelAt lab l)

def indexFiber (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (l : List (Vertex (p := p) (n := n))) (j : Fin m) : Finset (Fin l.length) :=
  Finset.univ.filter fun i => (labelAt lab l i).2 = j

theorem fiber_labelFace (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (l : List (Vertex (p := p) (n := n))) (j : Fin m) :
    fiber (labelFace lab l) j = (indexFiber lab l j).image (labelAt lab l) := by
  ext v
  simp only [fiber, labelFace, indexFiber, Finset.mem_filter, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hv⟩
    refine ⟨i, ?_, hi⟩
    rw [hi]
    exact hv
  · rintro ⟨i, hi, hiv⟩
    refine ⟨⟨i, hiv⟩, ?_⟩
    rw [← hiv]
    exact hi

theorem comparable_get (l : List (Vertex (p := p) (n := n)))
    (hl : IsStrictFlag l) (i k : Fin l.length) :
    l.get i ≤ l.get k ∨ l.get k ≤ l.get i := by
  rcases lt_trichotomy i k with hik | rfl | hki
  · exact Or.inl (hl.rel_get_of_lt hik).le
  · exact Or.inl le_rfl
  · exact Or.inr (hl.rel_get_of_lt hki).le

theorem low_fiber_card_le_one
    (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    (l : List (Vertex (p := p) (n := n))) (hl : IsStrictFlag l)
    (j : Fin m) (hj : j.val < alpha) :
    (fiber (labelFace lab l) j).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [fiber, Finset.mem_filter] at ha hb
  have ha' : ∃ i ∈ (Finset.univ : Finset (Fin l.length)), labelAt lab l i = a := by
    exact Finset.mem_image.mp ha.1
  have hb' : ∃ i ∈ (Finset.univ : Finset (Fin l.length)), labelAt lab l i = b := by
    exact Finset.mem_image.mp hb.1
  let i := Classical.choose ha'
  let k := Classical.choose hb'
  have hia : lab (l.get i) = a := (Classical.choose_spec ha').2
  have hkb : lab (l.get k) = b := (Classical.choose_spec hb').2
  have hia2 : (lab (l.get i)).2 = j := (congrArg Prod.snd hia).trans ha.2
  have hkb2 : (lab (l.get k)).2 = j := (congrArg Prod.snd hkb).trans hb.2
  rcases comparable_get l hl i k with hik | hki
  · have hlowi : (lab (l.get i)).2.val < alpha := by
      rw [hia2]
      exact hj
    have hsign := hadm.1 hik (hia2.trans hkb2.symm) hlowi
    calc
      a = lab (l.get i) := hia.symm
      _ = lab (l.get k) := Prod.ext hsign (hia2.trans hkb2.symm)
      _ = b := hkb
  · have hlowk : (lab (l.get k)).2.val < alpha := by
      rw [hkb2]
      exact hj
    have hsign := hadm.1 hki (hkb2.trans hia2.symm) hlowk
    calc
      a = lab (l.get i) := hia.symm
      _ = lab (l.get k) := Prod.ext hsign.symm (hia2.trans hkb2.symm)
      _ = b := hkb

theorem high_fiber_card_le
    (hp : p.Prime)
    (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    (l : List (Vertex (p := p) (n := n))) (hl : IsStrictFlag l)
    (hinj : Function.Injective (labelAt lab l))
    (j : Fin m) (hj : alpha ≤ j.val) :
    (fiber (labelFace lab l) j).card ≤ p - 1 := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rw [fiber_labelFace, Finset.card_image_of_injective _ hinj]
  by_contra hnot
  have hp_le : p ≤ (indexFiber lab l j).card := by omega
  obtain ⟨u, huI, hucard⟩ := Finset.exists_subset_card_eq hp_le
  let e : Fin p ≃o (u : Finset (Fin l.length)) := Finset.orderIsoOfFin u hucard
  let x : Fin p → Vertex (p := p) (n := n) := fun a => l.get (e a).1
  have hxmono : Monotone x := by
    intro a b hab
    by_cases hab' : a = b
    · subst b
      exact le_rfl
    · have halt : a < b := lt_of_le_of_ne hab hab'
      exact (hl.rel_get_of_lt (e.strictMono halt)).le
  have hxj : ∀ a, (lab (x a)).2 = j := by
    intro a
    have hmemI : (e a).1 ∈ indexFiber lab l j := huI (e a).2
    exact (Finset.mem_filter.mp hmemI).2
  have hsign_inj : Function.Injective (fun a => (lab (x a)).1) := by
    intro a b hab
    have hlab : lab (x a) = lab (x b) := Prod.ext hab ((hxj a).trans (hxj b).symm)
    have hidx : (e a).1 = (e b).1 := hinj hlab
    exact e.injective (Subtype.ext hidx)
  have hcard : Fintype.card (Fin p) = Fintype.card (ZMod p) := by simp [ZMod.card]
  have hsign_surj : Function.Surjective (fun a => (lab (x a)).1) :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨hsign_inj, hcard⟩ |>.2
  exact hadm.2 x hxmono ⟨j, hj, hxj⟩ hsign_surj

theorem labelFace_isAllowed
    (hp : p.Prime)
    (lab : Vertex (p := p) (n := n) → Label (p := p) (m := m))
    (hadm : IsAlphaAdmissible alpha lab)
    (l : List (Vertex (p := p) (n := n))) (hl : IsStrictFlag l)
    (hinj : Function.Injective (labelAt lab l)) :
    IsAllowed alpha (labelFace lab l) := by
  intro j
  by_cases hj : j.val < alpha
  · simpa [capacity, hj] using low_fiber_card_le_one lab hadm l hl j hj
  · simpa [capacity, hj] using high_fiber_card_le hp lab hadm l hl hinj j (by omega)

end

end LabelAllowed
