import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.IntervalCases

import Ramsey2lemmas.Sym2

import FormalRamsey.Ramsey2Color

namespace Int

-- NOTE: Imported from the future (v4.22.0)
protected theorem sub_eq_iff_eq_add {b a c : Int} : a - b = c ↔ a = c + b := by omega

protected lemma isAddUnit : ∀ z : ℤ, IsAddUnit z := by
  intro z
  use ⟨z, -z, by simp, by simp⟩

end Int

namespace SimpleGraph

-- NOTE: Missing in Mathlib
theorem IsIndepSet.subset {G : SimpleGraph V} (h : t ⊆ s) : G.IsIndepSet s → G.IsIndepSet t := Set.Pairwise.mono h

-- NOTE: Missing in Mathlib
@[simp]
theorem isNIndepSet_one {G : SimpleGraph V} : G.IsNIndepSet 1 s ↔ ∃ a, s = {a} := by
  simp only [isNIndepSet_iff, Finset.card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

-- FIXME: Why is this section called FintypeVGraph if the type is not finite?
section FintypeVGraph

variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

section Iso

variable {W : Type*} (G' : SimpleGraph W)

lemma Iso.IsClique (iso : G ≃g G') : G.IsClique s ↔ G'.IsClique (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsClique, Set.Pairwise]
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

lemma Iso.IsIndepSet (iso : G ≃g G') : G.IsIndepSet s ↔ G'.IsIndepSet (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

lemma Iso.IsNClique (iso : G ≃g G') : G.IsNClique n s ↔ G'.IsNClique n (s.map iso.toEquiv) := by simp [isNClique_iff, iso.IsClique]

lemma Iso.IsNIndepSet (iso : G ≃g G') : G.IsNIndepSet n s ↔ G'.IsNIndepSet n (s.map iso.toEquiv) := by simp [isNIndepSet_iff, iso.IsIndepSet]

lemma Iso.cliqueNum (iso : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
  unfold SimpleGraph.cliqueNum
  congr
  ext n
  simp
  apply Iff.intro
  · intro Gclique
    obtain ⟨S, Sprop⟩ := Gclique
    use (S.map iso.toEquiv)
    rw [iso.IsNClique] at Sprop
    assumption
  · intro Gclique'
    obtain ⟨S', Sprop'⟩ := Gclique'
    use (S'.map iso.toEquiv.symm)
    simpa [iso.IsNClique, Finset.map_map]

lemma Iso.indepNum (iso : G ≃g G') : G.indepNum = G'.indepNum := by
  unfold SimpleGraph.indepNum
  congr
  ext n
  simp
  apply Iff.intro
  · intro Gindep
    obtain ⟨S, Sprop⟩ := Gindep
    use (S.map iso.toEquiv)
    rw [iso.IsNIndepSet] at Sprop
    assumption
  · intro Gindep'
    obtain ⟨S', Sprop'⟩ := Gindep'
    use (S'.map iso.toEquiv.symm)
    simpa [iso.IsNIndepSet, Finset.map_map]

def Iso.compl (iso : G ≃g G') : Gᶜ ≃g G'ᶜ := by
  use iso
  intro u v
  simp [not_iff_not, ← iso.map_rel_iff']

end Iso

-- an (x,y)-graph on n vertices iff does not have clique of size x or independet set of size y
def isXYGraph : Prop := G.cliqueNum < x ∧ G.indepNum < y

noncomputable def RamseyOld : ℕ := sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)) (_ : DecidableRel G.Adj), G.isXYGraph x y}

theorem Lemma₁ : G.isXYGraph x y ↔ Gᶜ.isXYGraph y x := by
  simp [isXYGraph, indepNum]
  tauto

variable [Fintype V]

lemma exists_isNClique_of_le_cliqueNum  {n : ℕ} (h : n ≤ G.cliqueNum) : ∃ S : Finset V, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma exists_isNIndset_of_le_indepNum  {n : ℕ} (h : n ≤ G.indepNum) : ∃ S : Finset V, G.IsNIndepSet n S := by
  rcases G.exists_isNIndepSet_indepNum with ⟨s, sindset⟩
  have nlescard : n ≤ s.card := by simp [h, sindset.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNIndepSet_iff]
  exact sindset.isIndepSet.subset tprop.left

lemma cliqueNum2CliqueFree: G.cliqueNum < x ↔ G.CliqueFree x := by
  simp [CliqueFree, isNClique_iff]
  apply Iff.intro
  · intros H_cliqueNum S SIsClique
    linarith [SIsClique.card_le_cliqueNum]
  · intro NotXClique
    obtain ⟨S, SMaxClique⟩ := G.maximumClique_exists
    have SCardEqCN := maximumClique_card_eq_cliqueNum S SMaxClique
    simp [isMaximumClique_iff] at SMaxClique
    have SCardNEx := NotXClique S SMaxClique.left
    rw [SCardEqCN] at SCardNEx
    rcases Nat.lt_or_gt_of_ne (Ne.symm SCardNEx) with h | h
    · obtain ⟨T, TClique⟩ := exists_isNClique_of_le_cliqueNum G (Nat.le_of_lt h)
      simp [G.isNClique_iff] at TClique
      have contra := NotXClique T TClique.left
      simp_all
    · assumption

theorem noXYGraphIffRamseyGraphProp (N: ℕ) : (∀ (G : SimpleGraph (Fin N)), ¬ G.isXYGraph x y) ↔ RamseyGraphProp N x y := by
  simp [isXYGraph, RamseyGraphProp]
  apply Iff.intro
  · intros H G
    cases Nat.lt_or_ge G.cliqueNum x with
    | inl cnltx =>
      right
      exact exists_isNIndset_of_le_indepNum _ (H G cnltx)
    | inr cngex =>
      simp at cngex
      left
      exact exists_isNClique_of_le_cliqueNum _ cngex
  · intros H G cnltx
    cases H G with
    | inl xclique =>
      rcases xclique with ⟨S, xnclique⟩
      have xlecn := xnclique.isClique.card_le_cliqueNum
      simp [xnclique.card_eq] at xlecn
      have absurd := Nat.lt_of_le_of_lt xlecn cnltx
      simp at absurd
    | inr yindset =>
      rcases yindset with ⟨T, ynindset⟩
      rw [← ynindset.card_eq]
      exact ynindset.isIndepSet.card_le_indepNum

lemma isXYGraph_bddAbove : BddAbove {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x y} := by
  simp [BddAbove, upperBounds, Set.Nonempty]
  rcases (Ramsey₂Finite x y) with ⟨N, NRamsey⟩
  simp at NRamsey
  use N
  intros M G Gxy
  cases Nat.le_or_ge M N with
  | inl _ => assumption
  | inr MgeN =>
    have MRamsey : RamseyGraphProp M x y := by
      suffices Ramsey₂Prop M x y by rwa [← Ramsey₂GraphProp]
      exact Ramsey.RamseyMonotone NRamsey MgeN
    rw [← noXYGraphIffRamseyGraphProp] at MRamsey
    cases MRamsey G Gxy

lemma cardLERamseyOld [DecidableEq V] : G.isXYGraph x y → Fintype.card V ≤ RamseyOld x y := by
  cases (Nat.eq_zero_or_pos (Fintype.card V)) with
  | inl Vempty => simp [Vempty]
  | inr Vnonempty =>
    intro Gxy
    simp [RamseyOld]
    apply le_csSup
    · exact isXYGraph_bddAbove x y
    · simp [SimpleGraph.isXYGraph] at Gxy ⊢
      use G.overFin rfl
      simpa [← (G.overFinIso rfl).cliqueNum, ← (G.overFinIso rfl).indepNum]

------------------------------------------------ RamseyOld <-> GraphRamsey
variable {G}

lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card V
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

lemma fintype_indepNum_bddAbove : BddAbove {n | ∃ s, G.IsNIndepSet n s} := by
  use Fintype.card V
  rintro y ⟨s, syc⟩
  rw [isNIndepSet_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

theorem GraphRamsey2RamseyOld : GraphRamsey x.succ y.succ = RamseyOld x.succ y.succ + 1 := by
  simp [GraphRamsey]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  . simp_all
    apply And.intro
    · simp [← noXYGraphIffRamseyGraphProp]
      intro G Gxy
      have GinSup : (sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} + 1) ∈ {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} := by
        simp
        have fineq : Fintype.card (Fin (RamseyOld x.succ y.succ + 1)) = sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} + 1:= by simp [RamseyOld]
        use G.overFin fineq
        simpa [SimpleGraph.isXYGraph, ← (G.overFinIso fineq).cliqueNum, ← (G.overFinIso fineq).indepNum]
      have absurd := le_csSup (isXYGraph_bddAbove x.succ y.succ) GinSup
      simp at absurd
    · simp [RamseyGraphProp]
      cases {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ}.eq_empty_or_nonempty with
      | inl e =>
        have Rxy0 : Fintype.card (Fin 0) = RamseyOld x.succ y.succ := by simp [RamseyOld, e]
        use (⊥ : SimpleGraph (Fin 0)).overFin Rxy0
        apply And.intro
        · intro xset xNClique
          rcases xNClique with ⟨xclique, xcard⟩
          have xsetcardpos : 0 < xset.card := by simp [xcard]
          rw [Finset.card_pos] at xsetcardpos
          rcases xsetcardpos with ⟨absurd, _⟩
          simp [← Rxy0] at absurd
          apply finZeroElim absurd
        · intro yset yNClique
          rcases yNClique with ⟨yclique, ycard⟩
          have ysetcardpos : 0 < yset.card := by simp [ycard]
          rw [Finset.card_pos] at ysetcardpos
          rcases ysetcardpos with ⟨absurd, _⟩
          simp [← Rxy0] at absurd
          apply finZeroElim absurd
      | inr ne =>
        have sSup_mem := Nat.sSup_mem ne (isXYGraph_bddAbove x.succ y.succ)
        simp at sSup_mem
        rcases sSup_mem with ⟨G, Gxy⟩
        have fineq : Fintype.card (Fin (sSup {N | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph (x + 1) (y + 1)})) = RamseyOld x.succ y.succ := by simp [RamseyOld]
        use G.overFin fineq
        simp [SimpleGraph.isXYGraph] at Gxy
        apply And.intro
        · intro xset xNClique
          rcases xNClique with ⟨xsetclique, xsetcard⟩
          have cliqueNum_bound := xsetclique.card_le_cliqueNum
          simp [xsetcard, ← (G.overFinIso fineq).cliqueNum] at cliqueNum_bound
          have absurd : x + 1 < x + 1 := Nat.lt_of_le_of_lt cliqueNum_bound Gxy.left
          simp at absurd
        · intro yset yNIndepSet
          have indepNum_bound := yNIndepSet.isIndepSet.card_le_indepNum
          simp [yNIndepSet.card_eq, ← (G.overFinIso fineq).indepNum] at indepNum_bound
          have absurd : y + 1 < y + 1 := Nat.lt_of_le_of_lt indepNum_bound Gxy.right
          simp at absurd
  · simp
    intro M N MleqN MRamsey
    exact RamseyGraphMonotone MRamsey MleqN

theorem RamseyOld₂ : ∀ y : ℕ, RamseyOld 2 y.succ = y := by
  intro y
  suffices RamseyOld 2 y.succ + 1 = y + 1 by
    simp at this; simp[this]
  rw [← GraphRamsey2RamseyOld 1 y]
  simp
  exact GraphRamsey2 (y)

variable (i : ℕ) (G) [DecidableRel G.Adj]

noncomputable abbrev vᵢ : ℕ := RamseyOld x y.succ - i

noncomputable abbrev sᵢ : ℕ := (Finset.univ).filter (λ v ↦ G.degree v = vᵢ x y i) |>.card

noncomputable abbrev tᵢ (p : V): ℕ := (G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ x y i) |>.card

variable {G x y}
noncomputable def σ_G (_ : G.isXYGraph x.succ y.succ) : ℕ := RamseyOld x y.succ - G.minDegree

lemma sum_degree_eq_sum_over_degrees :
  ∑ v : V, G.degree v =
    ∑ d ∈ Finset.image (λ v => G.degree v) Finset.univ, d * ((Finset.univ).filter (λ v => G.degree v = d)).card := by

    have h_sigma : (∑ v: V, G.degree v) =
    ∑ p ∈ Finset.sigma (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v =>  G.degree v = d)), G.degree p.2 := by
      apply Finset.sum_bij (λ v hv => ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]

    rw [h_sigma]

    have h_inner_sum : ∀ d ∈ (Finset.image (λ v => G.degree v) Finset.univ),
    (∑ v ∈ (Finset.univ.filter (λ v => G.degree v = d)), G.degree v) =
    d * ((Finset.univ).filter (λ v => G.degree v = d)).card := by
      intros d hd
      have h : ∀ v ∈ (Finset.univ.filter (λ v => G.degree v = d)), G.degree v = d := by
        intros v hv
        rw [Finset.mem_filter] at hv
        rcases hv with ⟨hv1, hv2⟩
        rw [hv2]
      rw [Finset.sum_const_nat h]
      apply mul_comm

    suffices
      (∑ p ∈ Finset.sigma  (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v => G.degree v = d)), G.degree p.2) =
      (∑ d ∈ (Finset.image (λ v => G.degree v) Finset.univ), ∑ v ∈ Finset.univ.filter (λ v =>  G.degree v = d), G.degree v) by
      rw [this]
      apply Finset.sum_congr rfl h_inner_sum
    simp [Finset.sum_sigma']

lemma num_of_vertices_eq_sum_over_degrees : Fintype.card V =
  ∑ d ∈ Finset.image (λ v => G.degree v) Finset.univ, ((Finset.univ).filter (λ v => G.degree v = d)).card := by
  transitivity (∑ v: V, 1)
  simp
  have h_sigma : (∑ v: V, 1) =
    ∑ p ∈ Finset.sigma (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v =>  G.degree v = d)), 1 := by
      apply Finset.sum_bij (λ v hv => ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]
  rw [h_sigma]
  suffices
      (∑ p ∈ Finset.sigma  (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v => G.degree v = d)), 1) =
      (∑ d ∈ (Finset.image (λ v => G.degree v) Finset.univ), ∑ v ∈ Finset.univ.filter (λ v =>  G.degree v = d), 1) by
      rw [this]
      apply Finset.sum_congr rfl (by simp)
  simp [Finset.sum_sigma']
end FintypeVGraph
----------------------------------

section FinNGraph
variable (G : SimpleGraph (Fin N))[DecidableRel G.Adj] (p : Fin N)

def H₁ : SimpleGraph ↑(G.neighborSet p) := G.induce (G.neighborSet p)
instance H₁AdjDecidableRel : DecidableRel (H₁ G p).Adj := by apply instDecidableComapAdj

def H₂ : SimpleGraph ↑(Gᶜ.neighborSet p) := G.induce (Gᶜ.neighborSet p)
instance H₂AdjDecidableRel : DecidableRel (H₂ G p).Adj := by apply instDecidableComapAdj

abbrev e₁ : ℕ := (H₁ G p).edgeFinset.card
abbrev e₂ : ℕ := (H₂ G p).edgeFinset.card

end FinNGraph

section NonEmptyGraph

variable {x y N : ℕ} (G : SimpleGraph (Fin N.succ))(p : Fin N.succ)

lemma oneLeCN: 1 ≤ G.cliqueNum := by
  apply le_csSup fintype_cliqueNum_bddAbove
  simp
  tauto

lemma oneLeISN: 1 ≤ G.indepNum := by
  apply le_csSup fintype_indepNum_bddAbove
  simp
  tauto

lemma indepNumMono : (H₁ G p).indepNum ≤ G.indepNum := by
  simp [indepNum]
  apply csSup_le_csSup'
  · exact fintype_indepNum_bddAbove
  · rintro n ⟨S, SProp⟩
    simp
    use S.map (Function.Embedding.subtype _)
    simp [isNIndepSet_iff, IsIndepSet] at SProp ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ha_mem⟩
      rcases hb with ⟨hb, hb_mem⟩
      simp[Set.Pairwise] at SProp
      have _ := SProp.left a ha ha_mem b hb hb_mem hab
      tauto
    · exact SProp.right

variable [DecidableRel G.Adj]
lemma cliqueNumMono : (H₁ G p).cliqueNum ≤ G.cliqueNum - 1 := by
    simp [cliqueNum]
    rw [csSup_le_iff' fintype_cliqueNum_bddAbove]
    by_contra! H
    obtain ⟨n, ⟨ S, SClique⟩, SProp⟩ := H
    suffices ∃ s, G.IsNClique n.succ s by
      have tmp : n.succ ∈ {n | ∃ s, G.IsNClique n s} := by simp[this]
      have contra := le_csSup fintype_cliqueNum_bddAbove (tmp)
      rw [← @Nat.sub_le_sub_iff_right 1 (sSup {n | ∃ s, G.IsNClique n s}) n.succ] at contra
      simp_all; linarith
      exact oneLeCN G
    use insert p (S.map (Function.Embedding.subtype _))
    apply IsNClique.insert

    --TODO: refactor this?
    simp [isNClique_iff, IsClique] at SClique ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ha_mem⟩
      rcases hb with ⟨hb, hb_mem⟩
      simp[Set.Pairwise] at SClique
      have _ := SClique.left a ha ha_mem b hb hb_mem hab
      tauto
    · exact SClique.right

    simp_all

theorem Lemma₂ : G.isXYGraph x.succ y.succ →  G.degree p ≤ RamseyOld x y.succ ∧ G.degree p + RamseyOld x.succ y ≥ N := by
  intros xyGraphProp
  apply And.intro
  · have H₁isXYGraph: (H₁ G p).isXYGraph x y.succ := by
      have indepNum_mono := indepNumMono G p
      have cliqueNum_mono := cliqueNumMono G p
      simp [isXYGraph] at xyGraphProp ⊢
      simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at xyGraphProp
      simp [lt_of_le_of_lt indepNum_mono xyGraphProp.right]
      linarith
    have tmp := (cardLERamseyOld (H₁ G p) x y.succ H₁isXYGraph)
    rw [card_neighborSet_eq_degree] at tmp
    exact tmp
  · have H₁isXYGraph_C : (H₁ Gᶜ p)ᶜ.isXYGraph x.succ y := by
      have indepNum_mono := indepNumMono Gᶜ p
      have cliqueNum_mono := cliqueNumMono Gᶜ p
      simp at indepNum_mono cliqueNum_mono
      rw [Lemma₁] at xyGraphProp ⊢
      simp [isXYGraph] at xyGraphProp ⊢
      simp [← Nat.sub_lt_sub_iff_right (oneLeISN G)] at xyGraphProp
      apply And.intro
      · apply Nat.lt_of_le_of_lt cliqueNum_mono
        exact xyGraphProp.left
      · apply Nat.lt_of_le_of_lt indepNum_mono
        exact xyGraphProp.right
    have tmp := (cardLERamseyOld (H₁ Gᶜ p)ᶜ x.succ y H₁isXYGraph_C)
    simp [-Fintype.card_ofFinset, card_neighborSet_eq_degree, G.degree_compl p, Nat.add_comm] at tmp ⊢
    assumption

lemma G_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : Fin N.succ, G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.sᵢ x y j * vᵢ x y j := by
  rw [sum_degree_eq_sum_over_degrees]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.sᵢ x y j > 0) , G.sᵢ x y j * vᵢ x y j)
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a
    apply And.intro
    · rw [Nat.lt_add_one_iff]
      apply Nat.sub_le_sub_left
      apply G.minDegree_le_degree
    · simp [Finset.Nonempty, vᵢ]
      use a
      exact (Nat.sub_sub_self (Lemma₂ G a hxy).left).symm
  · simp
    intros a₁ a₂ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp [Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    rw [ha]
    exact Nat.sub_sub_self (Nat.le_trans hb (Nat.sub_le _ _))
  · simp [vᵢ]
    intros a
    simp [Nat.sub_sub_self (Lemma₂ G a hxy).left, mul_comm, sᵢ]
  · rw [Finset.sum_filter (λ j ↦ G.sᵢ x y j > 0) (λ j ↦ ↑(G.sᵢ x y j) * vᵢ x y j)]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    left
    assumption

lemma G_vertCount_eq (hxy : G.isXYGraph x.succ y.succ) : N.succ = (∑ i ∈ Finset.range (σ_G hxy + 1), G.sᵢ x y i ) := by
  transitivity Fintype.card (Fin N.succ)
  simp
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.sᵢ x y j > 0) , G.sᵢ x y j)
  rw [@num_of_vertices_eq_sum_over_degrees (Fin N.succ) G]
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp [σ_G]
    intro a
    apply And.intro
    · rw [Nat.lt_add_one_iff]
      apply Nat.sub_le_sub_left
      apply G.minDegree_le_degree
    · simp [Finset.Nonempty, vᵢ]
      use a
      symm
      exact Nat.sub_sub_self (Lemma₂ G a hxy).left
  · simp
    intros a₁ a₂ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    rw [ha]
    exact Nat.sub_sub_self (Nat.le_trans hb (Nat.sub_le _ _))
  · simp [vᵢ]
    intros a
    simp [-Fintype.card_ofFinset, sᵢ, vᵢ, Nat.sub_sub_self (Lemma₂ G a hxy).left]
  · rw [Finset.sum_filter (λ j ↦ G.sᵢ x y j > 0) (λ j ↦ (G.sᵢ x y j))]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp [sᵢ]
    exact (Finset.card_eq_zero.mpr h).symm

lemma H₁_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v ∈ (G.neighborFinset p), G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.tᵢ x y j p * vᵢ x y j := by
  suffices ∑ v  ∈ (G.neighborFinset p), G.degree v = ∑ d ∈ Finset.image (λ v ↦ G.degree v) (G.neighborFinset p), d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card by
    rw [this]
    transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.tᵢ x y j p > 0) , G.tᵢ x y j p * vᵢ x y j)
    apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
    · simp[σ_G]
      intros a ha
      apply And.intro
      · rw [Nat.lt_add_one_iff]
        apply Nat.sub_le_sub_left
        apply G.minDegree_le_degree
      · simp [Finset.Nonempty, vᵢ]
        use a
        refine ⟨ha, ?_⟩
        simp [Nat.sub_sub_self (Lemma₂ G a hxy).left]
    · simp
      intros a₁ _ a₂ _ h
      exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
    · simp[σ_G]
      intros b hb h
      rw [Nat.lt_succ_iff] at hb
      simp [Finset.Nonempty, vᵢ] at h
      obtain ⟨a, ha⟩ := h
      use a
      refine ⟨ha.left, ?_⟩
      rw [ha.right, Nat.sub_sub_self (Nat.le_trans hb (Nat.sub_le _ _))]
    · simp [vᵢ]
      intros a ha
      simp [Nat.sub_sub_self (Lemma₂ G a hxy).left, mul_comm, tᵢ]
    · rw [Finset.sum_filter (λ j ↦ G.tᵢ x y j p > 0) (λ j ↦ ↑(G.tᵢ x y j p) * vᵢ x y j)]
      apply Finset.sum_bij (λ j _ ↦ j) <;> simp
      intros a ha h
      left
      assumption
  have h_sigma : (∑ v ∈ (G.neighborFinset p), G.degree v) = ∑ p ∈ Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), G.degree p.2 := by
    apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
    intros a ha
    refine ⟨?_, ha⟩
    use a
    intros p _ _ _ _ _
    use p.2
    simp_all
  rw [h_sigma]
  have h_inner_sum : ∀ d ∈ ((G.neighborFinset p).image (λ v ↦ G.degree v)),
  (∑ v ∈ ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v) =
  d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card := by
    intros d hd
    have h : ∀ v ∈ ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v = d := by
      intros v hv
      rw [Finset.mem_filter] at hv
      rcases hv with ⟨hv1, hv2⟩
      rw [hv2]
    rw [Finset.sum_const_nat h]
    apply mul_comm
  suffices (∑ p ∈ Finset.sigma  ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree p.2) =
    (∑ d ∈ ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v ∈ (G.neighborFinset p).filter (λ v ↦  G.degree v = d), G.degree v) by
    rw [this]
    apply Finset.sum_congr rfl h_inner_sum
  simp [Finset.sum_sigma']

lemma H₁_vertCount_eq (hxy : G.isXYGraph x.succ y.succ) : ↑(Fintype.card ↑(G.neighborSet p)) = (∑ i ∈ Finset.range (σ_G hxy + 1), G.tᵢ x y i p) := by
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.tᵢ x y j p > 0) , G.tᵢ x y j p)
  transitivity (∑ d ∈ (G.neighborFinset p).image (fun v ↦ G.degree v), ((G.neighborFinset p).filter (fun v ↦ G.degree v = d)).card)
  · transitivity (∑ v : (G.neighborSet p), 1)
    simp
    have h_sigma : (∑ v: (G.neighborSet p), 1) =
      ∑ p ∈ Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), 1 := by
        apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
        intros a ha
        refine ⟨?_, ha⟩
        use a
        intros p _ _ _ _ _
        use p.2
        simp_all
    rw [h_sigma]
    suffices (∑ p ∈ Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), 1) = (∑ d ∈ ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v ∈ (G.neighborFinset p).filter (λ v ↦  G.degree v = d), 1) by
      rw [this]
      apply Finset.sum_congr rfl (by simp)
    simp [Finset.sum_sigma']
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a ha
    apply And.intro
    · rw [Nat.lt_add_one_iff]
      apply Nat.sub_le_sub_left
      apply G.minDegree_le_degree
    · simp [Finset.Nonempty, vᵢ]
      use a
      refine ⟨ha, ?_⟩
      simp [Nat.sub_sub_self (Lemma₂ G a hxy).left]
  · simp
    intros a₁ _ a₂ _ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp [σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp [Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    refine ⟨ha.left, ?_⟩
    simp [ha.right, Nat.sub_sub_self (Nat.le_trans hb (Nat.sub_le _ _))]
  · intros a ha
    simp at ha
    obtain ⟨b, ⟨_, bdeg⟩⟩ := ha
    simp [vᵢ, ← bdeg, Nat.sub_sub_self (Lemma₂ G b hxy).left, tᵢ]
  · rw [Finset.sum_filter (λ j ↦ G.tᵢ x y j p > 0) (λ j ↦ G.tᵢ x y j p)]
    simp [tᵢ, vᵢ]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp [h]

variable {G}

theorem Prop₁ (hxy : G.isXYGraph x.succ y.succ):
N.succ ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 - (σ_G hxy) ∧ (σ_G hxy) ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 -  N.succ := by
  obtain ⟨p, hp⟩ := G.exists_minimal_degree_vertex
  have ⟨ha, hb⟩ := (Lemma₂ G p hxy)
  simp[σ_G]
  apply And.intro
  rw[Nat.le_sub_iff_add_le (by simp; linarith)]
  have vLERamseyOld : G.minDegree ≤ RamseyOld x y.succ := by rw [← hp] at ha; exact ha
  rw [← Nat.add_sub_assoc vLERamseyOld]
  simp_all
  linarith
  suffices  0 ≤ (RamseyOld x.succ y + G.minDegree - N) by
    have temp : N ≤ RamseyOld x.succ y + G.minDegree := by
      simp [← hp, Nat.sub_le_iff_le_add] at hb
      linarith
    have temp1 : RamseyOld x y.succ ≤ RamseyOld x y.succ := by simp
    have temp2 := Nat.add_le_add temp1 this
    rw [← Nat.add_sub_assoc temp (RamseyOld x y.succ)] at temp2
    rw [← Nat.add_assoc (RamseyOld x y.succ) (RamseyOld x.succ y) G.minDegree] at temp2
    have temp3: N ≤ RamseyOld x y.succ + RamseyOld x.succ y := by linarith
    rw [← Nat.sub_add_comm temp3]
    assumption
  rw [← hp] at hb
  simp [hb]

variable (x y i)
open Finset

lemma pairs_to_degree : ∀ u, #(Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ)) = G.degree u := by
  intros u
  unfold SimpleGraph.degree
  apply Finset.card_nbij (λ e ↦ e.2)
  · simp
  · simp [Set.InjOn]
  -- NOTE: You would think all of this follows from simps but most any simp here causes maxHeartbeats errors
  · simp [Set.SurjOn]
    rw [Set.subset_def]
    intros v vadj
    simp at vadj
    rw [Set.mem_image]
    use (u, v)
    rw [Set.mem_image]
    apply And.intro
    · use v
      simpa
    · trivial

set_option maxHeartbeats 300000

theorem Prop₂ (hxy : G.isXYGraph x.succ y.succ) (iub : i ≤ RamseyOld x y.succ) (hp: G.degree p = vᵢ x y i) : 2 * (((e₂ G p : ℤ)  - e₁ G p)) =
RamseyOld x y.succ * (N.succ - 2 * (RamseyOld x y.succ) + 2 * i) + ∑ j ∈ Finset.range (σ_G hxy).succ, j * (2 * (tᵢ G x y j p) - (sᵢ G x y j : ℤ)) := by
  suffices step1: Fintype.card (↑G.edgeSet ⊕ ↑(G.induce (G.neighborSet p)).edgeSet) = Fintype.card ({ e : Fin N.succ × Fin N.succ | G.Adj e.fst e.snd ∧ e.fst ∈ G.neighborSet p } ⊕ ↑(G.induce (Gᶜ.neighborSet p)).edgeSet) by
    have step2 : ∀ e, e ∈ (Finset.biUnion (G.neighborFinset p) (λ u ↦ Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ))) ↔ e ∈ { e | G.Adj e.fst e.snd ∧ e.fst ∈ G.neighborSet p } := by
      intro e
      simp
      apply Iff.intro
      · intro ⟨u, ⟨uadj, ⟨v, ⟨vadj, euv⟩⟩⟩⟩
        simp [← euv]
        tauto
      · intro
        use e.1
        apply And.intro
        · tauto
        · use e.2
          tauto
    have step3 : #(Finset.biUnion (G.neighborFinset p) (λ u ↦ Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ))) = Finset.sum (G.neighborFinset p) (G.degree ·) := by
      suffices #(Finset.biUnion (G.neighborFinset p) (λ u ↦ Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ))) = Finset.sum (G.neighborFinset p) (λ u ↦ #(Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ))) by
        trans Finset.sum (G.neighborFinset p) (λ u ↦ (Finset.image (u, ·) (Finset.filter (G.Adj u ·) Finset.univ)).card)
        · assumption
        · apply Finset.sum_congr
          · trivial
          · intros u _
            apply pairs_to_degree
      apply Finset.card_biUnion
      intros u uadj v vadj uneqv
      intros x xinl xinr
      simp [Finset.subset_iff] at xinl xinr ⊢
      intros u' v' uvinx'
      simp [Eq.trans (xinl u' v' uvinx').right (xinr u' v' uvinx').right.symm] at uneqv
    simp only [Fintype.card_sum, Fintype.card_of_finset' _ step2, step3, H₁_degreeCount_eq G p hxy] at step1
    rw [← Nat.mul_right_inj (by simp : 2 ≠ 0), Nat.mul_add, Fintype.card_of_finset' _ (λ _ ↦ G.mem_edgeFinset),  ← sum_degrees_eq_twice_card_edges, G_degreeCount_eq G hxy, Nat.add_comm] at step1
    simp only [Nat.mul_sub_left_distrib, Fintype.card_of_finset' _ (λ _ ↦ (induce (G.neighborSet p) G).mem_edgeFinset), Fintype.card_of_finset' _ (λ _ ↦ (induce (Gᶜ.neighborSet p) G).mem_edgeFinset)] at step1
    have subNonneg (f : ℕ → [DecidableRel G.Adj] → ℕ) : ∀ k ∈ Finset.range (σ_G hxy + 1), f k * k ≤ (f k) * RamseyOld x (y + 1) := by
      simp [sᵢ, σ_G, Nat.lt_add_one_iff]
      intros x₁ x₁le
      apply Nat.mul_le_mul_left
      apply Nat.le_trans x₁le (Nat.sub_le _ _)
    rw [Finset.sum_tsub_distrib _ (subNonneg (G.sᵢ x y)), Finset.sum_tsub_distrib _ (subNonneg (λ z ↦ G.tᵢ x y z p)), Nat.mul_add] at step1
    zify at step1
    rw [← IsAddUnit.sub_eq_sub_iff (Int.isAddUnit _) (Int.isAddUnit _), ← neg_inj, Int.neg_sub, Int.neg_sub, ← Int.mul_sub 2, Int.natCast_sub (Finset.sum_le_sum (subNonneg (G.sᵢ x y))), Int.natCast_sub (Finset.sum_le_sum (subNonneg (λ z ↦ G.tᵢ x y z p))), ← Finset.sum_mul, ← Finset.sum_mul ,  (G_vertCount_eq G hxy).symm, ← H₁_vertCount_eq, G.card_neighborSet_eq_degree p, hp, Nat.cast_sum, Nat.cast_sum] at step1
    simp only [e₁, e₂, H₁, H₂, vᵢ, step1, Int.ofNat_eq_coe, Nat.cast_sum, Int.mul_sub]
    rw [Finset.mul_sum, ← sub_add, Int.sub_sub, sub_add, ← sub_add_eq_add_sub, ← Finset.sum_sub_distrib, ← Int.sub_sub, sub_right_comm, Int.natCast_mul _ (RamseyOld x (y + 1)), Int.natCast_mul _ (RamseyOld x (y + 1)), ← Int.mul_assoc _ _ (RamseyOld x (y + 1)), ← Int.sub_mul, Int.mul_comm, Int.natCast_sub iub]
    -- FIXME: Maybe do this with conv since it is specifically targeted to the sum
    simp only [Int.natCast_mul, ← Int.mul_assoc, ← Int.sub_mul, Int.mul_comm]
    simp +arith
    rw [Int.add_comm, ← Int.sub_eq_add_neg, Int.sub_eq_zero]
    simp +arith [Int.mul_comm]
  · apply @Fintype.card_of_bijective _ _ _ _ (λ e ↦ match e with | Sum.inl e' => (match Sym2.decBex (λ v ↦ G.Adj p v) ↑e' with | isTrue padj => Sum.inl ⟨if G.Adj p e'.val.toOrderedPair.fst then e'.val.toOrderedPair else e'.val.toOrderedPair.swap,  by have eedge := e'.prop; rw [e'.val.toOrderedPair_repr] at eedge padj; rw [G.mem_edgeSet] at eedge; split; simp [eedge]; assumption; simp [G.adj_symm eedge]; rw [Sym2.exists_mem_pair] at padj; simp_all⟩ | isFalse pnotadj => Sum.inr ⟨e'.val.pmap (λ v (vine' : v ∈ e'.val) ↦ ⟨v, by simp; rw [← not_or]; intro pcases; cases pcases with | inl peqv => have e'repr := Sym2.other_spec vine'; have padj := (↑e' : G.edgeSet).prop; rw [← e'repr, G.mem_edgeSet] at padj; simp [peqv] at pnotadj; apply pnotadj (Sym2.Mem.other vine') (Sym2.other_mem vine'); assumption | inr padj => have e'prop := e'.prop; apply pnotadj; use v⟩) (by simp), by cases e' with | mk e' e'edge => cases e' with | h u v => simp [Sym2.pmap, Quot.recOn, Quot.rec]; simp at e'edge; assumption⟩) | Sum.inr e' => Sum.inl ⟨(e'.val.map (·.val)).toOrderedPair.swap, by cases e' with | mk e' e'prop => cases e' with | h u v => have uvcases := @Sym2.toOrderedPair_repr (Fin N.succ) _ s(↑u, ↑v); simp at uvcases; cases uvcases with | inl uv => simp [← uv] at e'prop ⊢; rw [G.adj_comm]; have pv := v.prop; rw [G.mem_neighborSet] at pv; tauto | inr vu => simp [← vu] at e'prop ⊢; have pu := u.prop; rw [G.mem_neighborSet] at pu; tauto⟩)
    apply And.intro
    · intros a b fabeq
      simp at fabeq
      split at fabeq
      next e' =>
        split at fabeq
        · split at fabeq
          · split at fabeq
            · congr
              split at fabeq
              · simp at fabeq
                split at fabeq
                · exact Subtype.val_inj.mp (Sym2.toOrderedPair_inj fabeq)
                · cases G.not_isDiag_of_mem_edgeSet e'.prop (Sym2.toOrderedPair_IsDiag_of_eq fabeq).left
              · simp at fabeq
            · simp at fabeq
              cases G.not_isDiag_of_mem_edgeSet e'.prop (Sym2.toOrderedPair_IsDiag_of_eq fabeq).left
          · split at fabeq
            next =>
              split at fabeq
              · simp at fabeq
                split at fabeq
                · symm at fabeq
                  cases G.not_isDiag_of_mem_edgeSet e'.prop (Sym2.toOrderedPair_IsDiag_of_eq fabeq).right
                · simp at fabeq
                  congr
                  exact Subtype.val_inj.mp (Sym2.toOrderedPair_inj fabeq)
              · simp at fabeq
            next e'' =>
              simp at fabeq
              have e''prop := e''.prop
              rw [e''.val.toOrderedPair_repr, SimpleGraph.mem_edgeSet] at e''prop
              have e''fst := e''.val.toOrderedPair.fst.prop
              have e''snd := e''.val.toOrderedPair.snd.prop
              rw [G.mem_neighborSet] at e''fst e''snd
              have e'mapped := Sym2.toOrderedPair_inj fabeq
              rw [e'.val.toOrderedPair_repr, e''.val.toOrderedPair_repr, Sym2.map_pair_eq, Sym2.eq_iff] at e'mapped
              cases e'mapped with
              | inl e'fst =>
                rw [← e'fst.left] at e''fst
                contradiction
              | inr e'snd =>
                rw [← e'snd.left] at e''snd
                contradiction
        · split at fabeq
          · split at fabeq
            · simp at fabeq
            · simp at fabeq
              congr
              ext u
              have matcher : ∀ {β γ : Type} {P : γ → Prop} {u : β} {v : β} {f : (b : γ) → P b → β} {e : Sym2 γ} {h}, s(u, v) = Sym2.pmap f e h → u ∈ Sym2.pmap f e h := by
                intros β γ P u v f e h pmapeq
                have repl := Sym2.mem_mk_left u v
                rw [pmapeq] at repl
                assumption
              apply Iff.intro <;> intro uine' <;> simp (config := { singlePass := true }) [← Sym2.other_spec uine'] at fabeq
              · conv at fabeq =>
                  lhs
                  simp [Sym2.pmap, Quot.recOn, Quot.rec]
                have matched := matcher fabeq
                simp at matched
                assumption
              · conv at fabeq =>
                  rhs
                  simp [Sym2.pmap, Quot.recOn, Quot.rec]
                have matched := matcher fabeq.symm
                simp at matched
                assumption
          · simp at fabeq
      next e' =>
        split at fabeq
        next e'' =>
          split at fabeq
          · simp at fabeq
            split at fabeq
            · cases (G.not_isDiag_of_mem_edgeSet e''.prop) (Sym2.toOrderedPair_IsDiag_of_eq fabeq.symm).left
            · simp at fabeq
              have e'prop := e'.prop
              rw [e'.val.toOrderedPair_repr, SimpleGraph.mem_edgeSet] at e'prop
              have e'fst := e'.val.toOrderedPair.fst.prop
              have e'snd := e'.val.toOrderedPair.snd.prop
              rw [G.mem_neighborSet] at e'fst e'snd
              have e''mapped := Sym2.toOrderedPair_inj fabeq
              rw [e'.val.toOrderedPair_repr, e''.val.toOrderedPair_repr, Sym2.map_pair_eq, Sym2.eq_iff] at e''mapped
              cases e''mapped with
              | inl e''fst =>
                rw [e''fst.left] at e'fst
                contradiction
              | inr e''snd =>
                rw [e''snd.right] at e'snd
                contradiction
          · simp at fabeq
        next =>
          simp at fabeq
          have mapeq := Sym2.toOrderedPair_inj fabeq
          congr
          ext u
          have matcher : ∀ {β γ : Type} {u : β} {v : β} {f : (b : γ) → β} {e : Sym2 γ}, s(u, v) = e.map f → u ∈ Sym2.map f e := by
            intros β γ u v f e mapeq
            have repl := Sym2.mem_mk_left u v
            rw [mapeq] at repl
            assumption
          apply Iff.intro <;> intro uine' <;> simp (config := { singlePass := true }) [← Sym2.other_spec uine'] at mapeq
          · have matched := matcher mapeq
            simp at matched
            exact matched.right
          · have matched := matcher mapeq.symm
            simp at matched
            exact matched.right
    · intros e
      cases e with
      | inl e =>
        if pAdjsnd : G.Adj p e.val.snd then
         have pAdjfst := e.prop.right
         simp at pAdjfst
         cases Fin.instLinearOrder.decidableLE e.val.fst e.val.snd with
         | isTrue eordered =>
           use Sum.inl ⟨s(e.val.fst ⊓ e.val.snd, e.val.fst ⊔ e.val.snd), by rw [G.mem_edgeSet, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]; exact e.prop.left⟩
           simp
           split
           next =>
             congr
             split
             next =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered, Sym2.exists_mem_pair] at notadj
               have pAdjfst := e.prop.right
               simp at pAdjfst
               contradiction
           next _ _ pnotadj _ =>
             simp only [min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered, Sym2.exists_mem_pair, not_or] at pnotadj
             have pAdjfst := e.prop.right
             simp at pAdjfst
             cases pnotadj.left pAdjfst
         | isFalse eswapped =>
           use Sum.inr ⟨s(⟨e.val.fst, pAdjfst⟩, ⟨e.val.snd, pAdjsnd⟩), e.prop.left⟩
           simp at eswapped
           simp [← Subtype.val_inj, Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)]
       else
         cases Fin.instLinearOrder.decidableLE e.val.fst e.val.snd with
         | isTrue eordered =>
           simp at eordered
           use Sum.inl ⟨s(e.val.fst ⊓ e.val.snd, e.val.fst ⊔ e.val.snd), by rw [G.mem_edgeSet, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]; exact e.prop.left⟩
           simp
           split
           next padj _ =>
             congr
             split
             next =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec] at notadj
               simp only [min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered, Sym2.exists_mem_pair] at notadj padj
               simp [pAdjsnd, notadj] at padj
           next _ _ pnotadj _ =>
             simp only [min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered, Sym2.exists_mem_pair, not_or] at pnotadj
             have pAdjfst := e.prop.right
             simp at pAdjfst
             cases pnotadj.left pAdjfst
         | isFalse eswapped =>
           simp at eswapped
           use Sum.inl ⟨s(e.val.fst ⊔ e.val.snd, e.val.fst ⊓ e.val.snd), by rw [G.mem_edgeSet, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)]; exact e.prop.left⟩
           simp
           split
           next padj _ =>
             congr
             split
             next absurd =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)] at absurd
               contradiction
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.recOn, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)]
           next _ _ pnotadj _ =>
             simp only [min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped), Sym2.exists_mem_pair, not_or] at pnotadj
             have pAdjfst := e.prop.right
             simp at pAdjfst
             cases pnotadj.left pAdjfst
      | inr e =>
        use Sum.inl ⟨e.val.map (·.val), by cases uv : e.val with | h u v => have uvedge := e.prop; simp [uv] at uvedge; assumption⟩
        simp
        split
        next padj _ =>
          simp
          cases uv : e.val with
          | h u v =>
            simp [uv] at padj
            have uprop := u.prop
            have vprop := v.prop
            simp only [SimpleGraph.neighborSet, Set.mem_setOf, SimpleGraph.compl_adj] at uprop vprop
            simp [uprop.right, vprop.right] at padj
        next => aesop

theorem Corollary₂  (hxy : G.isXYGraph 3 y.succ) (iub : i ≤ RamseyOld 2 y.succ) (hp: G.degree p = vᵢ 2 y i) :
  2 * e₂ G p = ↑y * ((↑N.succ) - 2 * ↑y + 2 * ↑i) + ∑ j ∈ Finset.range (σ_G hxy).succ, (↑j : ℤ) * (2 * ↑ (tᵢ G 2 y j p) - ↑(sᵢ G 2 y j)) := by
  have Prop₂ := Prop₂ 2 y p i hxy iub hp
  suffices tmp: G.e₁ p = 0 ∧ RamseyOld 2 y.succ = y by
    rw [tmp.left, tmp.right] at Prop₂
    simp_all
  apply And.intro
  · simp [Finset.filter_eq_empty_iff]
    by_contra H
    simp at H
    obtain ⟨⟨u, v⟩, uvProp⟩ := H
    simp [isXYGraph] at hxy
    suffices (G.H₁ p).cliqueNum < 2 by
      simp [cliqueNum2CliqueFree, CliqueFree, isNClique_iff] at this
      have contra := this {u,v}
      simp [IsClique] at contra uvProp
      simp [uvProp] at contra
      rw [Finset.card_insert_of_not_mem] at contra
      · trivial
      · by_contra
        simp_all
    have H₁CliqueNum_UB := cliqueNumMono G p
    simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at hxy
    linarith
  · have tmp := GraphRamsey2 y
    simp [GraphRamsey2RamseyOld] at tmp
    exact tmp

-- theorem Prop₃ (hxy: G.isXYGraph 3 y) (h: ∃ u v: Fin N.succ, G.Adj u v ∧ G.degree u = (vᵢ 3 y i) ∧ G.degree v = (vᵢ 3 y i)):
--   let p := Exists.choose h -- use classical.choose, is this bad?
--   haveI : DecidableRel (H₂ G p).Adj := by apply  instDecidableComapAdj
--   let e₂ := (H₂ G p).edgeFinset.card
--   e₂ ≤ (y - 1) * (N.succ / 2 - y + 1 + i):= by
--   sorry

-- noncomputable def e_x_y_n (x y N : ℕ) : ℕ := sInf {n : ℕ | ∃ (G : SimpleGraph (Fin N.succ)) (_ : DecidableRel G.Adj), G.isXYGraph x y ∧ G.edgeFinset.card = n}

-- theorem Prop₄ (hxy: G.isXYGraph 3 y):
--   let e := G.edgeFinset.card
--   let sᵢ := λ i ↦ (Finset.univ : Finset (Fin N.succ)).filter (λ v ↦ G.degree v = vᵢ x y i) |>.card
--   let vᵢ := vᵢ 3 y i
--   N.succ * e ≥ (∑ i in Finset.range (σ_G hxy).succ, e_x_y_n 3 (y-1) (N.succ - vᵢ - 1) + vᵢ^2) * sᵢ i:= by
--   sorry

-- theorem Prop₃ (hxy: G.isXYGraph 3 y) (h: ∃ u v: Fin N.succ, G.Adj u v ∧ G.degree u = (vᵢ 3 y i) ∧ G.degree v = (vᵢ 3 y i)):
--   let p := Exists.choose h -- use classical.choose, is this bad?
--   haveI : DecidableRel (H₂ G p).Adj := by apply  instDecidableComapAdj
--   let e₂ := (H₂ G p).edgeFinset.card
--   e₂ ≤ (y - 1) * (N.succ / 2 - y + 1 + i):= by
--   sorry

noncomputable def e (x y N : ℕ) : ℕ := sInf {n : ℕ | ∃ (G : SimpleGraph (Fin N.succ)) (_ : DecidableRel G.Adj), G.isXYGraph x y ∧ G.edgeFinset.card = n}

-- noncomputable def e (x y N : ℕ) : ℕ :=

--   let allGraphs : Finset (SimpleGraph (Fin N.succ)) := Finset.univ
--   haveI :  DecidablePred (fun (G : SimpleGraph (Fin (N.succ))) => G.isXYGraph x y) := by unfold isXYGraph; infer_instance
--   let xyGraphs := allGraphs.filter (fun(G : SimpleGraph (Fin (N.succ))) => G.isXYGraph x y )

--   let counts := xyGraphs.image (fun G => G.edgeSet.ncard)

--   if h : counts.Nonempty then
--     counts.min' h
--   else
--     0




theorem Prop₄ (hxy: G.isXYGraph 3 y.succ):
  N.succ * G.edgeFinset.card ≥ (∑ i ∈ Finset.range (σ_G hxy).succ, ((e 3 y (N - (vᵢ 2 y i) - 1) : ℤ) + (vᵢ 2 y i)^2) * sᵢ G 2 y i) := by
  sorry
  -- suffices step1: ∀ p : Fin N.succ, ∃ i, (G.degree p = vᵢ 2 y i ∧ ↑(#G.edgeFinset) ≥
  -- (↑(e_x_y_n 3 (y - 1) (↑N.succ - vᵢ 2 y i - 1).toNat) + vᵢ 2 y i ^ 2 + (∑ j in Finset.range (σ_G hxy).succ, ((((i - j) : ℤ) * ((G.tᵢ 2 y i p): ℤ))))))
  -- · conv =>
  --     lhs
  --     simp only [G_vertCount_eq G hxy]

  --   suffices step2 : ∑ p : Fin N.succ, (∑ j in Finset.range (σ_G hxy).succ, ((((i - j) : ℤ) * ((G.tᵢ 2 y i p): ℤ)))) * (sᵢ G 2 y i) = 0


    -- push_cast
    -- rw [ge_iff_le, Nat.add_one, Finset.sum_mul]
    -- apply Finset.sum_le_sum

    -- intros i hi
    -- rw[mul_comm]
    -- by_cases h : G.sᵢ 2 y i = 0
    -- simp [h]
    -- rw[mul_le_mul_left]
    -- simp[sᵢ] at h
    -- replace h := Finset.nonempty_iff_ne_empty.mpr h
    -- obtain ⟨p, hp⟩ := h
    -- -- simp at hp
    -- have :=  step1 p
    -- rcases this with ⟨ _ , ⟨_, this⟩⟩
    -- exact ge_iff_le.mp this
  --   omega

  -- · intros i hi




  -- rw []
  -- ↑(G.sᵢ x y i)

-- example (h1 : 27 * e ≥ 85 * s0 + 80 * s1 + 75 * s2 + 75 * s3)
-- (h1 : 2 * e ≤ 7 * s0 + 6 * s1 + 5 * s2 + 4 * s3)
-- (h3 : s0 + s1 + s2 + s3 = 27) :
-- e ≥ 80 := by linarith

theorem R37 : RamseyOld 3 7 = 22 := sorry

lemma e37_18 : e 3 7 18 ≥ 36 := by sorry
lemma e37_19 : e 3 7 19 ≥ 44 := by sorry
lemma e37_20 : e 3 7 20 ≥ 50 := by sorry
lemma e37_21 : e 3 7 21 ≥ 59 := by sorry

lemma Ineq₉_helper {G : SimpleGraph (Fin 27)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 8)
(_ : e 3 7 18 ≥ 36)
(_ : e 3 7 19 ≥ 44)
(_ : e 3 7 20 ≥ 50)
(_ : e 3 7 21 ≥ 59):
G.edgeFinset.card ≥ 80 := by
  have hr := RamseyOld₂ 7

  have h1 := Prop₄ 7 hxy
  simp [-Set.toFinset_card] at h1
  replace : σ_G hxy ≤ 3 := by
    have := (Prop₁ hxy).2
    simp [hr] at this
    rw [R37] at this
    omega

  have h2 :=  G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy

  interval_cases σ_G hxy
  · simp [Finset.range, vᵢ, hr, -Set.toFinset_card] at h1
    replace h1 : 27 * G.edgeFinset.card ≥ 85 * (↑(G.sᵢ 2 7 0) : ℤ ):= by
      suffices (↑(e 3 7 18) + 49) * ↑(G.sᵢ 2 7 0) ≥ 85 * ↑(G.sᵢ 2 7 0) by
        linarith
      gcongr
      linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 0) = 27 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 27 * G.edgeFinset.card ≥ 85 * (↑(G.sᵢ 2 7 0) : ℤ ) + 80 * ↑(G.sᵢ 2 7 1):= by
      suffices (↑(e 3 7 19) + 36) * ↑(G.sᵢ 2 7 1) + (↑(e 3 7 18) + 49) * ↑(G.sᵢ 2 7 0) ≥ 80 * ↑(G.sᵢ 2 7 1) + 85 * ↑(G.sᵢ 2 7 0)by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +  6 * ↑(G.sᵢ 2 7 1) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0) = 27 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 27 * G.edgeFinset.card ≥ 85 * (↑(G.sᵢ 2 7 0) : ℤ ) + 80 * ↑(G.sᵢ 2 7 1) + 75 * ↑(G.sᵢ 2 7 2):= by
      suffices (↑(e 3 7 20) + 25) * ↑(G.sᵢ 2 7 2) +
      (↑(e 3 7 19) + 36) * ↑(G.sᵢ 2 7 1) +
       (↑(e 3 7 18) + 49) * ↑(G.sᵢ 2 7 0)
       ≥  75 * ↑(G.sᵢ 2 7 2) + 80 * ↑(G.sᵢ 2 7 1) + 85 * ↑(G.sᵢ 2 7 0) by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +  6 * ↑(G.sᵢ 2 7 1) + 5 * ↑(G.sᵢ 2 7 2):= by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 2) + ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0)  = 27 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp [vᵢ, hr, Finset.range, ←Nat.add_assoc, -Set.toFinset_card] at h1
    replace h1 : 27 * G.edgeFinset.card ≥ 85 * ↑(G.sᵢ 2 7 0) + 80 * ↑(G.sᵢ 2 7 1) + 75 * ↑(G.sᵢ 2 7 2) + 75 * (G.sᵢ 2 7 3) := by
      suffices (↑(e 3 7 21) + 16) * ↑(G.sᵢ 2 7 3) + (↑(e 3 7 20) + 25) * ↑(G.sᵢ 2 7 2) +
        (↑(e 3 7 19) + 36) * ↑(G.sᵢ 2 7 1) +
      (↑(e 3 7 18) + 49) * ↑(G.sᵢ 2 7 0) ≥
            75 * (G.sᵢ 2 7 3) + 75 * ↑(G.sᵢ 2 7 2) + 80 * ↑(G.sᵢ 2 7 1) + 85 * ↑(G.sᵢ 2 7 0) by
        linarith
      simp
      gcongr <;>linarith


    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +
      6 * ↑(G.sᵢ 2 7 1) +
        5 * ↑(G.sᵢ 2 7 2) +
          4  * ↑(G.sᵢ 2 7 3) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 3) + ↑(G.sᵢ 2 7 2) + ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0) = 27 := by
      simp[this, Finset.range] at h3
      linarith

    linarith

theorem Ineq₉:
e 3 8 26 ≥ 80 := by
  simp only [e]
  sorry
  -- apply le_csInf
  -- simp [Set.Nonempty, -Set.toFinset_card, isXYGraph]
  -- use sorry
  -- let G := readG6 "Z????CDO?a@PHA_HcE_dc`PCXQ@PoSWo@_cDS_YQQB_Qo?TLSO?q_g?{p?_?"
  -- use G
  -- apply And.intro
  -- have : G.cliqueFinset 3 = Finset.empty := by native_decide
  -- native_decide

  -- sorry
  -- simp [-Set.toFinset_card]
  -- intro N G hxy _ hn
  -- have := Ineq₉_helper hxy h1 h2 h3 h4
  -- omega

lemma Ineq₁₀_helper {G : SimpleGraph (Fin 28)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 8)
(_ : e 3 7 19 ≥ 44)
(_ : e 3 7 20 ≥ 50)
(_ : e 3 7 21 ≥ 59):
G.edgeFinset.card ≥ 88 := by
  have hr := RamseyOld₂ 7

  have h1 := Prop₄ 7 hxy
  simp [-Set.toFinset_card] at h1
  replace : σ_G hxy ≤ 2 := by
    have := (Prop₁ hxy).2
    rw [R37] at this
    simp [hr] at this
    omega

  have h2 :=  G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy

  interval_cases σ_G hxy
  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 28 * G.edgeFinset.card ≥ 93 * (↑(G.sᵢ 2 7 0) : ℤ ):= by
      suffices (↑(e 3 7 19) + 49) * ↑(G.sᵢ 2 7 0) ≥ 93 * ↑(G.sᵢ 2 7 0) by
        linarith
      gcongr
      linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 0) = 28 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp[vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 28 * G.edgeFinset.card ≥ 93 * (↑(G.sᵢ 2 7 0) : ℤ ) + 86 * ↑(G.sᵢ 2 7 1):= by
      suffices (↑(e 3 7 20) + 36) * ↑(G.sᵢ 2 7 1) + (↑(e 3 7 19) + 49) * ↑(G.sᵢ 2 7 0) ≥ 86 * ↑(G.sᵢ 2 7 1) + 93 * ↑(G.sᵢ 2 7 0)by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +  6 * ↑(G.sᵢ 2 7 1) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0) = 28 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp[vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 28 * G.edgeFinset.card ≥ 93 * (↑(G.sᵢ 2 7 0) : ℤ ) + 86 * ↑(G.sᵢ 2 7 1) + 84 * ↑(G.sᵢ 2 7 2):= by
      suffices (↑(e 3 7 21) + 25) * ↑(G.sᵢ 2 7 2) +
      (↑(e 3 7 20) + 36) * ↑(G.sᵢ 2 7 1) +
       (↑(e 3 7 19) + 49) * ↑(G.sᵢ 2 7 0)
       ≥  84 * ↑(G.sᵢ 2 7 2) + 86 * ↑(G.sᵢ 2 7 1) + 93 * ↑(G.sᵢ 2 7 0) by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +  6 * ↑(G.sᵢ 2 7 1) + 5 * ↑(G.sᵢ 2 7 2):= by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega
    replace h3 : ↑(G.sᵢ 2 7 2) + ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0)  = 28 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

theorem Ineq₁₀:
e 3 8 27 ≥ 88 := by
  simp only [e]
  sorry
  -- apply le_csInf
  -- simp [Set.Nonempty, -Set.toFinset_card]
  -- sorry
  -- simp [-Set.toFinset_card]
  -- intro N G hxy _ hn
  -- have := Ineq₉_helper hxy h1 h2 h3 h4
  -- omega

lemma Ineq₁₁_helper {G : SimpleGraph (Fin 29)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 8)
(_ : e 3 7 20 ≥ 50)
(_ : e 3 7 21 ≥ 59):
G.edgeFinset.card ≥ 99 := by
  have hr := RamseyOld₂ 7

  have h1 := Prop₄ 7 hxy
  simp [-Set.toFinset_card] at h1
  replace : σ_G hxy ≤ 1 := by
    have := (Prop₁ hxy).2
    simp [hr] at this
    have : RamseyOld 3 7 ≤ 22 := by sorry
    omega

  have h2 :=  G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy

  interval_cases σ_G hxy
  · simp[vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 29 * G.edgeFinset.card ≥ 99 * (↑(G.sᵢ 2 7 0) : ℤ ):= by
      suffices (↑(e 3 7 20) + 49) * ↑(G.sᵢ 2 7 0) ≥ 99 * ↑(G.sᵢ 2 7 0) by
        linarith
      gcongr
      linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 0) = 29 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp[vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 29 * G.edgeFinset.card ≥ 99 * (↑(G.sᵢ 2 7 0) : ℤ ) + 95 * ↑(G.sᵢ 2 7 1):= by
      suffices (↑(e 3 7 21) + 36) * ↑(G.sᵢ 2 7 1) + (↑(e 3 7 20) + 49) * ↑(G.sᵢ 2 7 0) ≥ 95 * ↑(G.sᵢ 2 7 1) + 99 * ↑(G.sᵢ 2 7 0)by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 7 * ↑(G.sᵢ 2 7 0) +  6 * ↑(G.sᵢ 2 7 1) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 7 1) + ↑(G.sᵢ 2 7 0) = 29 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

theorem Ineq₁₁:
e 3 8 28 ≥ 99 := by
  simp only [e]
  sorry

theorem R39Ineq {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
G.edgeFinset.card ≥ 144 := by
  have hr := RamseyOld₂ 8

  have h1 := Prop₄ 8 hxy
  simp [-Set.toFinset_card] at h1
  replace : σ_G hxy ≤ 2 := by
    have := (Prop₁ hxy).2
    simp [hr] at this
    have : RamseyOld 3 8 ≤ 29 := by
      simp [RamseyOld]
      apply csSup_le
      sorry
      simp
      intro N G hxy
      sorry
    omega

  have h2 := G_degreeCount_eq G hxy
  have h3 := G_vertCount_eq G hxy
  have _ := Ineq₉
  have _ := Ineq₁₀
  have _ := Ineq₁₁

  interval_cases σ_G hxy
  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ):= by
      suffices (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0) ≥ 144 * ↑(G.sᵢ 2 8 0) by
        linarith
      gcongr
      linarith

    replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 8 0) = 36 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ) + 137 * ↑(G.sᵢ 2 8 1):= by
      suffices (↑(e 3 8 27) + 49) * ↑(G.sᵢ 2 8 1) + (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0) ≥ 137 * ↑(G.sᵢ 2 8 1) + 144 * ↑(G.sᵢ 2 8 0)by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) +  7 * ↑(G.sᵢ 2 8 1) := by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 8 1) + ↑(G.sᵢ 2 8 0) = 36 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

  · simp [vᵢ, hr, Finset.range, -Set.toFinset_card] at h1
    replace h1 : 36 * G.edgeFinset.card ≥ 144 * (↑(G.sᵢ 2 8 0) : ℤ ) + 137 * ↑(G.sᵢ 2 8 1) + 135 * ↑(G.sᵢ 2 8 2):= by
      suffices (↑(e 3 8 28) + 36) * ↑(G.sᵢ 2 8 2) +
      (↑(e 3 8 27) + 49) * ↑(G.sᵢ 2 8 1) +
       (↑(e 3 8 26) + 64) * ↑(G.sᵢ 2 8 0)
       ≥  135 * ↑(G.sᵢ 2 8 2) + 137 * ↑(G.sᵢ 2 8 1) + 144 * ↑(G.sᵢ 2 8 0) by
        linarith
      gcongr <;>linarith

    replace h2 : 2 * G.edgeFinset.card = 8 * ↑(G.sᵢ 2 8 0) +  7 * ↑(G.sᵢ 2 8 1) + 6 * ↑(G.sᵢ 2 8 2):= by
      simp at h2
      rw [← sum_degrees_eq_twice_card_edges, h2]
      simp[Finset.range, vᵢ, hr]
      omega

    replace h3 : ↑(G.sᵢ 2 8 2) + ↑(G.sᵢ 2 8 1) + ↑(G.sᵢ 2 8 0)  = 36 := by
      simp[this, Finset.range] at h3
      linarith
    linarith

lemma R3y_neighbor_Ind {G : SimpleGraph (Fin N.succ)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 y.succ) :
  ∀ p : Fin (N.succ),  G.IsNIndepSet (G.degree p) (G.neighborFinset p) := by
  intro p
  by_contra! absurd
  simp [isNIndepSet_iff, isIndepSet_iff, Set.Pairwise] at absurd
  obtain ⟨u, adj_up, v,adj_vp, v_neq_u, adj_uv⟩ := absurd

  have hx := (csSup_le_iff' fintype_cliqueNum_bddAbove).mp (Nat.le_pred_of_lt hxy.1)
  simp at hx
  specialize hx 3 {p, u, v}
  suffices G.IsNClique 3 {p, u, v} by
    linarith [hx this]
  simp[isNClique_iff]
  have : p ≠ v := by by_contra!; simp[this] at adj_vp
  have : p ≠ u := by by_contra!; simp[this] at adj_up
  simp_all

theorem R39_36_graph_IsRegular8 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
  G.IsRegularOfDegree 8 := by
  simp[IsRegularOfDegree]
  have h_neighbor := R3y_neighbor_Ind 8 hxy

  have deg_le: ∀ p ∈ Finset.univ, G.degree p ≤ 8 := by
    intro p
    by_contra!
    simp[isXYGraph, cliqueNum, indepNum] at hxy
    have hy := (csSup_le_iff' fintype_indepNum_bddAbove).mp (Nat.le_pred_of_lt hxy.2)
    simp at hy
    specialize hy (G.degree p) (G.neighborFinset p)
    specialize h_neighbor p
    linarith [hy h_neighbor]

  have _ := R39Ineq hxy
  have h1 : 2 * 144 ≤ 2 * #G.edgeFinset := by linarith
  rw[← sum_degrees_eq_twice_card_edges] at h1
  norm_num at h1
  have h2 : ∑ v : Fin 36, G.degree v ≤ ∑ p : Fin 36, 8 := by
    apply Finset.sum_le_sum
    exact deg_le

  have sum_deg_eq : ∑ v : Fin 36, G.degree v = ∑ p : Fin 36, 8 := by norm_num at *; linarith
  have := (Finset.sum_eq_sum_iff_of_le deg_le).mp sum_deg_eq
  simp at this
  exact this

theorem R39_36_graph_has_R38_27 {G : SimpleGraph (Fin 36)} [DecidableRel G.Adj] (hxy: G.isXYGraph 3 9):
 ∃ (s : Finset (Fin 36)),s.card = 27 ∧ ((G.induce s).isXYGraph 3 8) := by
  use Gᶜ.neighborFinset 0
  simp [SimpleGraph.degree_compl, R39_36_graph_IsRegular8 hxy 0]
  simp[isXYGraph]
  by_contra! absurd
  simp [isXYGraph] at *
  by_cases hclique : (induce (↑(Gᶜ.neighborFinset 0)) G).cliqueNum < 3
  specialize absurd hclique
  suffices (induce (↑(Gᶜ.neighborFinset 0)) G).indepNum ≤ G.cliqueNum - 1 by
    omega
  simp [indepNum, cliqueNum]
  -- apply csInf_le
  sorry
  sorry
