import Mathlib.Data.Nat.Lattice
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.IntervalCases

import Ramsey2lemmas.Sym2

import FormalRamsey.Ramsey2Color

import SimplerGraph

namespace Int

protected lemma isAddUnit : ∀ z : ℤ, IsAddUnit z := by
  intro z
  use ⟨z, -z, by simp, by simp⟩

end Int

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

-- an (x,y)-graph on n vertices iff does not have clique of size x or independet set of size y
def isXYGraph : Prop := G.cliqueNum < x ∧ G.indepNum < y

noncomputable def RamseyOld : ℕ := sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)) (_ : DecidableRel G.Adj), G.isXYGraph x y}

theorem Lemma₁ : G.isXYGraph x y ↔ Gᶜ.isXYGraph y x := by
  simp [isXYGraph, indepNum]
  tauto

theorem noXYGraphIffRamseyGraphProp (N: ℕ) : (∀ (G : SimpleGraph (Fin N)), ¬ G.isXYGraph x y) ↔ RamseyGraphProp N x y := by
  simp [isXYGraph, RamseyGraphProp]
  apply Iff.intro
  · intros H G
    cases Nat.lt_or_ge G.cliqueNum x with
    | inl cnltx =>
      right
      exact exists_isNIndset_of_le_indepNum (H G cnltx)
    | inr cngex =>
      simp at cngex
      left
      exact exists_isNClique_of_le_cliqueNum cngex
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

variable [Fintype V]

lemma cardLERamseyOld : G.isXYGraph x y → Fintype.card V ≤ RamseyOld x y := by
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

lemma R3y_neighbor_Ind [DecidableEq V] [DecidableRel G.Adj] {y : ℕ} (hxy: G.isXYGraph 3 y.succ) : ∀ p,  G.IsNIndepSet (G.degree p) (G.neighborFinset p) := by
  intro p
  simp [G.isNIndepSet_iff, G.neighborFinset_def, SimpleGraph.degree]
  apply G.isIndepSet_neighborSet_of_triangleFree
  rw [← G.cliqueNum_lt_iff_cliqueFree]
  exact hxy.left

------------------------------------------------ RamseyOld <-> GraphRamsey

theorem GraphRamsey2RamseyOld : GraphRamsey x.succ y.succ = RamseyOld x.succ y.succ + 1 := by
  simp [GraphRamsey]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  . simp_all
    apply And.intro
    · simp [← noXYGraphIffRamseyGraphProp]
      intro G Gxy
      have GinSup : (sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} + 1) ∈ {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} := by
        have fineq : Fintype.card (Fin (RamseyOld x.succ y.succ + 1)) = sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)), G.isXYGraph x.succ y.succ} + 1:= by simp [RamseyOld]
        use G.overFin fineq
        simp [SimpleGraph.isXYGraph, ← (G.overFinIso fineq).cliqueNum, ← (G.overFinIso fineq).indepNum]
        simp [SimpleGraph.isXYGraph] at Gxy
        assumption
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
          have absurd : x + 1 < x + 1 := Nat.lt_of_le_of_lt cliqueNum_bound (Nat.lt_add_one_iff.mpr Gxy.left)
          simp at absurd
        · intro yset yNIndepSet
          have indepNum_bound := yNIndepSet.isIndepSet.card_le_indepNum
          simp [yNIndepSet.card_eq, ← (G.overFinIso fineq).indepNum] at indepNum_bound
          have absurd : y + 1 < y + 1 := Nat.lt_of_le_of_lt indepNum_bound (Nat.lt_add_one_iff.mpr Gxy.right)
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

variable (i : ℕ) [DecidableRel G.Adj]

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
  simp

----------------------------------

section Induced

variable [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] (p : α)

def H₁ : SimpleGraph ↑(G.neighborSet p) := G.induce (G.neighborSet p)

instance : DecidableRel (G.H₁ p).Adj := by apply instDecidableComapAdj

def H₂ : SimpleGraph ↑(Gᶜ.neighborSet p) := G.induce (Gᶜ.neighborSet p)

instance : DecidableRel (G.H₂ p).Adj := by apply instDecidableComapAdj

abbrev e₁ : ℕ := (H₁ G p).edgeFinset.card

abbrev e₂ : ℕ := (H₂ G p).edgeFinset.card

def H₁₂_iso : (G.H₁ p)ᶜ ≃g (Gᶜ.H₂ p) := {
  toFun := λ v ↦ ⟨v.val, by simp⟩,
  invFun := λ v ↦ ⟨v.val, by have := v.prop; simp [compl_compl] at this ⊢; assumption⟩,
  left_inv := by simp [Function.LeftInverse],
  right_inv := by simp [Function.RightInverse, Function.LeftInverse],
  map_rel_iff' := by simp [H₁, H₂]
}

-- NOTE: The linter flags [DecidableRel G.Adj] as unused which is
-- probably wrong because one cannot use H₁ without it.  This only
-- started appearing after the update to v4.22.0 so probably a
-- newly-introduced bug.
lemma H₁_eq_bot_of_3y (hxy : G.isXYGraph 3 y.succ) : ∀ p, G.H₁ p = ⊥ := by
  simp [← SimpleGraph.edgeSet_eq_empty, Set.eq_empty_iff_forall_notMem, H₁]
  intros p e eind
  cases e with
  | h u v =>
    simp at eind
    change G.Adj ↑u ↑v at eind
    have pu := u.prop
    have pv := v.prop
    simp [-Subtype.coe_prop] at pu pv
    have clique3 : G.IsNClique 3 {p, ↑u, ↑v} := by simp [G.is3Clique_triple_iff]; tauto
    have cnle3 := clique3.isClique.card_le_cliqueNum
    rw [clique3.card_eq] at cnle3
    cases (Nat.not_le_of_lt hxy.left) cnle3

end Induced

section Nonempty

variable {x y N : ℕ} (G : SimpleGraph (Fin N.succ)) (p : Fin N.succ) [DecidableRel G.Adj]

-- NOTE: The linter flags [DecidableRel G.Adj] as unused which is
-- probably wrong because one cannot use H₁ without it.  This only
-- started appearing after the update to v4.22.0 so probably a
-- newly-introduced bug.
lemma H₁_cliqueNum_lt : (H₁ G p).cliqueNum ≤ G.cliqueNum - 1 := by
  simp [Nat.le_iff_lt_add_one, ← Nat.sub_add_comm G.cliqueNum_pos]
  suffices clique_insert : ∀ S n', (G.H₁ p).IsNClique n' S → G.IsNClique n'.succ (insert p (S.map ⟨Subtype.val, by simp⟩)) by
    obtain ⟨S, SIsNClique⟩ := (G.H₁ p).exists_isNClique_cliqueNum
    obtain ⟨pSIsClique, pScard⟩ := clique_insert S (G.H₁ p).cliqueNum SIsNClique
    simp at pScard
    have psCard_le := pSIsClique.card_le_cliqueNum
    simp at psCard_le
    rw [Nat.lt_iff_add_one_le, ← pScard]
    exact psCard_le
  intro S n SIsNClique
  constructor
  · simp [SimpleGraph.isClique_iff, Set.Pairwise]
    apply And.intro
    · intro u pu uinS pnequ
      tauto
    · intros u pu uinS
      apply And.intro
      · simp [G.symm pu]
      · intros v pv vinS uneqv
        have sub_adj := SIsNClique.isClique uinS vinS
        simp [uneqv, H₁] at sub_adj
        exact sub_adj
  · simp [SIsNClique.card_eq]

theorem Lemma₂ : G.isXYGraph x.succ y.succ →  G.degree p ≤ RamseyOld x y.succ ∧ G.degree p + RamseyOld x.succ y ≥ N := by
  intros xyGraphProp
  apply And.intro
  · have H₁isXYGraph: (H₁ G p).isXYGraph x y.succ := by
      simp [isXYGraph] at xyGraphProp ⊢
      apply And.intro
      · apply Nat.lt_of_le_of_lt (H₁_cliqueNum_lt _ _)
        exact Nat.sub_one_lt_of_le (cliqueNum_pos G) xyGraphProp.left
      · trans G.indepNum
        · apply Embedding.indepNum_mono
          apply Embedding.induce
        · exact xyGraphProp.right
    have tmp := (cardLERamseyOld (H₁ G p) x y.succ H₁isXYGraph)
    rw [card_neighborSet_eq_degree] at tmp
    exact tmp
  · have H₁isXYGraph_C : (H₁ Gᶜ p)ᶜ.isXYGraph x.succ y := by
      have indepNum_mono := Embedding.indepNum_mono (by simp [H₁]; apply Embedding.induce : (G.H₁ p) ↪g G)
      have cliqueNum_mono := H₁_cliqueNum_lt Gᶜ p
      simp at indepNum_mono cliqueNum_mono
      rw [Lemma₁] at xyGraphProp ⊢
      simp [isXYGraph] at xyGraphProp ⊢
      apply And.intro
      · apply Nat.lt_of_le_of_lt cliqueNum_mono
        apply Nat.sub_one_lt_of_le (indepNum_pos _)
        exact xyGraphProp.left
      · trans G.cliqueNum
        · trans Gᶜ.indepNum
          · apply Embedding.indepNum_mono
            apply Embedding.induce
          · simp
        · exact xyGraphProp.right
    have tmp := (cardLERamseyOld (H₁ Gᶜ p)ᶜ x.succ y H₁isXYGraph_C)
    simp [-Fintype.card_ofFinset, card_neighborSet_eq_degree, G.degree_compl p, Nat.add_comm] at tmp ⊢
    assumption

lemma G_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : Fin N.succ, G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.sᵢ x y j * vᵢ x y j := by
  rw [sum_degree_eq_sum_over_degrees]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.sᵢ x y j > 0) , G.sᵢ x y j * vᵢ x y j)
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp [σ_G]
    intro a
    apply And.intro
    · rw [← Nat.sub_add_comm]
      · rw [Nat.add_sub_assoc]
        · simp
        · apply G.minDegree_le_degree
      · exact Nat.le_trans (G.minDegree_le_degree _) (Lemma₂ G a hxy).left
    · simp [Finset.Nonempty, vᵢ]
      use a
      exact (Nat.sub_sub_self (Lemma₂ G a hxy).left).symm
  · simp
    intros a₁ a₂ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp[σ_G]
    intros b hb h
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
    · rw [← Nat.sub_add_comm]
      · rw [Nat.add_sub_assoc]
        · simp
        · apply G.minDegree_le_degree
      · exact Nat.le_trans (G.minDegree_le_degree _) (Lemma₂ G a hxy).left
    · simp [Finset.Nonempty, vᵢ]
      use a
      symm
      exact Nat.sub_sub_self (Lemma₂ G a hxy).left
  · simp
    intros a₁ a₂ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp[σ_G]
    intros b hb h
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    rw [ha]
    exact Nat.sub_sub_self (Nat.le_trans hb (Nat.sub_le _ _))
  · simp
    intros a
    simp [-Fintype.card_ofFinset, sᵢ, vᵢ, Nat.sub_sub_self (Lemma₂ G a hxy).left]
  · rw [Finset.sum_filter (λ j ↦ G.sᵢ x y j > 0) (λ j ↦ (G.sᵢ x y j))]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    symm
    simp [sᵢ]
    exact h

lemma H₁_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v ∈ (G.neighborFinset p), G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.tᵢ x y j p * vᵢ x y j := by
  suffices ∑ v  ∈ (G.neighborFinset p), G.degree v = ∑ d ∈ Finset.image (λ v ↦ G.degree v) (G.neighborFinset p), d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card by
    rw [this]
    transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.tᵢ x y j p > 0) , G.tᵢ x y j p * vᵢ x y j)
    apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
    · simp[σ_G]
      intros a ha
      apply And.intro
      · rw [← Nat.sub_add_comm]
        · rw [Nat.add_sub_assoc]
          · simp
          · apply G.minDegree_le_degree
        · exact Nat.le_trans (G.minDegree_le_degree _) (Lemma₂ G a hxy).left
      · simp [Finset.Nonempty, vᵢ]
        use a
        refine ⟨ha, ?_⟩
        simp [Nat.sub_sub_self (Lemma₂ G a hxy).left]
    · simp
      intros a₁ _ a₂ _ h
      exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
    · simp[σ_G]
      intros b hb h
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
    simp
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a ha
    apply And.intro
    · rw [← Nat.sub_add_comm]
      · rw [Nat.add_sub_assoc]
        · simp
        · apply G.minDegree_le_degree
      · exact Nat.le_trans (G.minDegree_le_degree _) (Lemma₂ G a hxy).left
    · simp [Finset.Nonempty, vᵢ]
      use a
      refine ⟨ha, ?_⟩
      simp [Nat.sub_sub_self (Lemma₂ G a hxy).left]
  · simp
    intros a₁ _ a₂ _ h
    exact tsub_inj_right (Lemma₂ G a₁ hxy).left (Lemma₂ G a₂ hxy).left h
  · simp [σ_G]
    intros b hb h
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
    symm
    simp
    exact h

variable {G}

theorem Prop₁ (hxy : G.isXYGraph x.succ y.succ):
N.succ ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 - (σ_G hxy) ∧ (σ_G hxy) ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 -  N.succ := by
  obtain ⟨p, hp⟩ := G.exists_minimal_degree_vertex
  have ⟨ha, hb⟩ := (Lemma₂ G p hxy)
  simp[σ_G]
  apply And.intro
  · rw [Nat.lt_sub_iff_add_lt]
    have vLERamseyOld : G.minDegree ≤ RamseyOld x y.succ := by rw [← hp] at ha; exact ha
    rw [← Nat.add_sub_assoc vLERamseyOld]
    simp +arith
    linarith
  · suffices  0 ≤ (RamseyOld x.succ y + G.minDegree - N) by
      have temp : N ≤ RamseyOld x.succ y + G.minDegree := by
        simp [← hp] at hb
        linarith
      have temp1 : RamseyOld x y.succ ≤ RamseyOld x y.succ := by simp
      have temp2 := Nat.add_le_add temp1 this
      rw [← Nat.add_sub_assoc temp (RamseyOld x y.succ)] at temp2
      rw [← Nat.add_assoc (RamseyOld x y.succ) (RamseyOld x.succ y) G.minDegree] at temp2
      have temp3: N ≤ RamseyOld x y.succ + RamseyOld x.succ y := by linarith
      rw [← Nat.sub_add_comm temp3]
      assumption
    rw [← hp] at hb
    simp

open Finset

-- TODO: See if this is useable in Prop₂
lemma vᵢ_deg_swap {x y N : ℕ} {G : SimpleGraph (Fin N.succ)} [DecidableRel G.Adj] (hxy : G.isXYGraph x.succ y.succ) : ∀ (j : Fin N.succ) (d : Fin (σ_G hxy).succ), vᵢ x y (G.degree j) = d.val ↔ G.degree j = vᵢ x y d.val := by
  simp [vᵢ]
  intros v d
  apply Iff.intro
  · intro Rvd
    rw [← Rvd, Nat.sub_sub_self (Lemma₂ G v hxy).left]
  · intro Rdv
    rw [Rdv, Nat.sub_sub_self]
    trans σ_G hxy
    · rw [← Nat.lt_add_one_iff]
      exact d.prop
    · simp [σ_G]

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
            unfold SimpleGraph.degree
            apply Finset.card_nbij (λ e ↦ e.2) <;> simp [Set.InjOn, Set.SurjOn, Set.subset_def, Set.MapsTo]
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
      simp [σ_G]
      intros x₁ x₁le
      apply Nat.mul_le_mul_left
      apply Nat.le_trans x₁le (Nat.sub_le _ _)
    rw [Finset.sum_tsub_distrib _ (subNonneg (G.sᵢ x y)), Finset.sum_tsub_distrib _ (subNonneg (λ z ↦ G.tᵢ x y z p)), Nat.mul_add] at step1
    zify at step1
    rw [← IsAddUnit.sub_eq_sub_iff (Int.isAddUnit _) (Int.isAddUnit _), ← neg_inj, Int.neg_sub, Int.neg_sub, ← Int.mul_sub 2, Int.natCast_sub (Finset.sum_le_sum (subNonneg (G.sᵢ x y))), Int.natCast_sub (Finset.sum_le_sum (subNonneg (λ z ↦ G.tᵢ x y z p))), ← Finset.sum_mul, ← Finset.sum_mul ,  (G_vertCount_eq G hxy).symm, ← H₁_vertCount_eq, G.card_neighborSet_eq_degree p, hp, Nat.cast_sum, Nat.cast_sum] at step1
    simp only [e₁, e₂, H₁, H₂, vᵢ, step1, Int.mul_sub]
    rw [Finset.mul_sum, ← sub_add, Int.sub_sub, sub_add, ← sub_add_eq_add_sub, ← Finset.sum_sub_distrib, ← Int.sub_sub, sub_right_comm, Int.natCast_mul _ (RamseyOld x (y + 1)), Int.natCast_mul _ (RamseyOld x (y + 1)), ← Int.mul_assoc _ _ (RamseyOld x (y + 1)), ← Int.sub_mul, Int.mul_comm, Int.natCast_sub iub]
    rw [Int.sub_eq_add_neg]
    congr
    · simp +arith
    · simp [Int.mul_comm]
      congr
      ext x₁
      rw [Int.mul_comm, @Int.mul_comm 2]
      apply Int.mul_assoc
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
         cases Fin.decLe e.val.fst e.val.snd with
         | isTrue eordered =>
           use Sum.inl ⟨s(e.val.fst ⊓ e.val.snd, e.val.fst ⊔ e.val.snd), by rw [G.mem_edgeSet, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]; exact e.prop.left⟩
           simp
           split
           next =>
             congr
             split
             next =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered] at notadj
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
           simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)]
       else
         cases Fin.decLe e.val.fst e.val.snd with
         | isTrue eordered =>
           simp at eordered
           use Sum.inl ⟨s(e.val.fst ⊓ e.val.snd, e.val.fst ⊔ e.val.snd), by rw [G.mem_edgeSet, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]; exact e.prop.left⟩
           simp
           split
           next padj _ =>
             congr
             split
             next =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_left_iff.mpr eordered, max_eq_right_iff.mpr eordered]
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec] at notadj
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
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)] at absurd
               contradiction
             next notadj =>
               simp [Sym2.toOrderedPair, Sym2.rec, Quot.rec, min_eq_right_iff.mpr (Fin.le_of_lt eswapped), max_eq_left_iff.mpr (Fin.le_of_lt eswapped)]
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

noncomputable def e (x y N : ℕ) : ℕ := sInf {n : ℕ | ∃ (G : SimpleGraph (Fin N.succ)) (_ : DecidableRel G.Adj), G.isXYGraph x y ∧ G.edgeFinset.card = n}

lemma exy0 : ∀ (x y : ℕ), e x y 0 = 0 := by
  intros x y
  simp [e, Set.eq_empty_iff_forall_notMem]
  cases x with
  | zero =>
    right
    intros _ _ Gxy
    simp [isXYGraph] at Gxy
  | succ x =>
    cases x with
    | zero =>
      right
      intros _ G Gxy
      simp [isXYGraph] at Gxy
      have absurd := G.cliqueNum_pos
      simp [Gxy.left] at absurd
    | succ x =>
      cases y with
      | zero =>
        right
        intros _ _ Gxy
        simp [isXYGraph] at Gxy
      | succ y =>
        cases y with
        | zero =>
          right
          intros _ G Gxy
          simp [isXYGraph] at Gxy
          have absurd := G.indepNum_pos
          simp [Gxy.right] at absurd
        | succ y =>
          left
          simp [isXYGraph]

lemma e₂_ge_e (hxy: G.isXYGraph x.succ y.succ) : G.e₂ p ≥ e x.succ y (N - G.degree p).pred := by
  cases Nat.decLt (G.degree p) N with
  | isTrue Gdegplt =>
    simp only [e₂, e, GE.ge]
    have Gord : (Gᶜ.neighborFinset p).card = N - G.degree p - 1 + 1 := by
      simp [SimpleGraph.degree_compl, Nat.sub_sub]
      rw  [← tsub_tsub_assoc] <;> simp [Gdegplt]
    have finMap : ↑(Gᶜ.neighborSet p) ≃ { x // x ∈ Gᶜ.neighborFinset p } := by
      simp [SimpleGraph.neighborFinset, SimpleGraph.neighborSet]
      trivial
    have Giso := SimpleGraph.Iso.map (finMap.trans (Finset.equivFinOfCardEq Gord)) (G.H₂ p)
    rw [Giso.card_edgeFinset_eq]
    apply csInf_le (by simp)
    simp
    use (G.H₂ p).map (finMap.trans (Finset.equivFinOfCardEq Gord)).toEmbedding
    rw [Giso.card_edgeFinset_eq]
    apply And.intro
    · simp [-Equiv.trans_toEmbedding, isXYGraph, ← Giso.cliqueNum, ← Giso.indepNum]
      apply And.intro
      · rw [Nat.le_iff_lt_add_one]
        apply Nat.lt_of_le_of_lt _ hxy.left
        apply Embedding.cliqueNum_mono
        apply Embedding.induce
      · have Gcc := H₁₂_iso Gᶜ p
        rw [compl_compl G] at Gcc
        simp [← Gcc.indepNum]
        have Gccn := Nat.lt_of_le_sub_one (by simp [Nat.lt_iff_add_one_le, G.indepNum_pos]) (Gᶜ.H₁_cliqueNum_lt p)
        have Ginle := Nat.le_pred_of_lt hxy.right
        simp [isXYGraph] at hxy Gccn Ginle
        exact Nat.lt_of_lt_of_le Gccn Ginle
    · use (by infer_instance)
  | isFalse Gdegge =>
    simp at Gdegge
    have e0 : e x.succ y (N - G.degree p).pred = 0 := by simp [Nat.sub_eq_zero_of_le Gdegge, exy0]
    rw [e0]
    simp

theorem Prop₄ (hxy: G.isXYGraph 3 y.succ) : N.succ * G.edgeFinset.card ≥ (∑ i ∈ Finset.range (σ_G hxy).succ, (e 3 y (N - (vᵢ 2 y i) - 1) + (vᵢ 2 y i)^2) * sᵢ G 2 y i) := by
  -- NOTE: This is not quite H₁ because we want the vertex to be of type Fin N.succ
  let β : Fin N.succ → ℕ → ℕ := λ p j ↦ #((G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ 2 y j))
  have βsum_eq_card : ∀ (p : Fin (N + 1)), G.degree p = ∑ x : Fin (σ_G hxy + 1), β p ↑x := by
    intro p
    have βdisjoint : Set.PairwiseDisjoint ↑(Finset.range (σ_G hxy).succ) (λ j ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ 2 y j)) := by
      simp [Set.PairwiseDisjoint, Set.Pairwise, Disjoint]
      intros u ult v vlt uneqv s ssubu ssubv
      apply Finset.eq_empty_of_forall_notMem
      intros w wins
      have winu := ssubu wins
      have winv := ssubv wins
      simp at winu winv
      have absurd := Eq.trans winu.right.symm winv.right
      simp [vᵢ] at absurd
      simp [σ_G] at ult vlt
      cases uneqv (tsub_inj_right (Nat.le_trans ult (Nat.sub_le _ _)) (Nat.le_trans vlt (Nat.sub_le _ _)) absurd)
    have βsum_eq_card := Finset.card_disjiUnion (Finset.range (σ_G hxy).succ) (λ j ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ 2 y j)) βdisjoint
    simp [Finset.sum_range] at βsum_eq_card
    change ((range (σ_G hxy + 1)).biUnion (λ j ↦ filter (λ v ↦ G.degree v = vᵢ 2 y j) (G.neighborFinset p))).card = ∑ j : Fin (σ_G hxy).succ, β p ↑j at βsum_eq_card
    have range_biUnion_eq : (range (σ_G hxy + 1)).biUnion (λ j ↦ filter (λ v ↦ G.degree v = vᵢ 2 y j) (G.neighborFinset p)) = G.neighborFinset p := by
      ext v
      simp
      apply Iff.intro
      · tauto
      · intro pv
        use RamseyOld 2 y.succ - (G.degree v)
        simp [pv, vᵢ, σ_G, Nat.sub_sub_self (Lemma₂ G v hxy).left, ← Nat.sub_add_comm (Nat.le_trans (G.minDegree_le_degree v) (Lemma₂ G v hxy).left), Nat.add_sub_assoc (G.minDegree_le_degree v)]
    simp [range_biUnion_eq, β] at βsum_eq_card
    simp [βsum_eq_card, β]
  -- NOTE: Candidate for promotion to a proper lemma
  have vᵢjlt : ∀ j : Fin N.succ, vᵢ 2 y (G.degree j) < (σ_G hxy).succ := by
    intro j
    simp [σ_G]
    -- NOTE: Somehow this must be done in two steps
    simp [← Nat.sub_add_comm (Nat.le_trans (G.minDegree_le_degree j) (Lemma₂ G j hxy).left), Nat.add_sub_assoc (G.minDegree_le_degree j)]
  -- -- NOTE: This i is masking the global i because the global i does not work here
  have ecount : ∀ {i : Fin (σ_G hxy).succ} (p : Fin N.succ) (pdeg : G.degree p = vᵢ 2 y i.val), #G.edgeFinset + (Finset.sum Finset.univ (λ (j : Fin (σ_G hxy).succ) ↦ j.val * (β p j.val))) = e₂ G p + (vᵢ 2 y i)^2 + i * (Finset.sum Finset.univ (λ (j : Fin (σ_G hxy).succ) ↦ β p j.val)) := by
    intros i p pdeg
    -- NOTE: It is preposterous that one cannot lift embeddings in Sym2 given that
    -- this is  the only sane way to deal with (induced) subgraphs, etc.
    let revemb : Sym2 ↑(Gᶜ.neighborSet p) ↪ Sym2 (Fin N.succ) := { toFun := (λ e ↦ e.map Subtype.val), inj' := Sym2.map.injective (by simp) }
    have edecomp : G.edgeFinset = (G.H₂ p).edgeFinset.map revemb ∪ ((G.neighborFinset p).biUnion (λ j ↦ G.incidenceFinset j)) := by
      ext e
      simp
      apply Iff.intro
      · intros emem
        cases Sym2.Mem.decidable p e with
        | isTrue pine =>
          rw [Sym2.mem_iff_exists] at pine
          obtain ⟨q, pq⟩ := pine
          right
          use q
          simp [pq] at emem
          simp [SimpleGraph.incidenceSet, pq, emem]
        | isFalse pnotine =>
          cases ((G.neighborFinset p).filter (λ v ↦ v ∈ e)).decidableNonempty with
          | isTrue h1 =>
            obtain ⟨q, pq⟩ := h1
            simp at pq
            right
            use q
            simp [SimpleGraph.incidenceSet]
            tauto
          | isFalse h2 =>
            simp [Finset.eq_empty_iff_forall_notMem] at h2
            left
            use e.pmap (λ v vprop ↦ ⟨v, by simp; apply And.intro; intro peqv; simp [← peqv] at vprop; contradiction; intro pv; cases h2 v pv vprop⟩) (by simp)
            apply And.intro
            · simp [H₂]
              cases e with
              | h u v =>
                simp [Sym2.pmap_pair] at emem ⊢
                exact emem
            · simp [revemb]
              ext v
              simp [Sym2.mem_map]
              intros vine
              apply And.intro
              · intro peqv
                simp [← peqv] at vine
                contradiction
              · intro pv
                cases h2 v pv vine
      · intro ex
        cases ex with
        | inl exf =>
          obtain ⟨f, fprop⟩ := exf
          cases f with
          | h u v =>
            simp [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj, Function.Embedding.subtype_apply, H₂] at fprop
            simp [← fprop.right, revemb, fprop.left]
        | inr exv =>
          obtain ⟨v, vprop⟩ := exv
          exact G.incidenceSet_subset v vprop.right
    have edecompdisj : Disjoint ((G.H₂ p).edgeFinset.map revemb) ((G.neighborFinset p).biUnion (λ j ↦ G.incidenceFinset j)) := by
      simp [Finset.disjoint_iff_ne, revemb]
      intros e eedge f v pv finc eeqf
      simp [SimpleGraph.incidenceSet] at finc
      simp [← eeqf] at finc
      obtain ⟨⟨_, contra⟩, _⟩ := finc.right
      contradiction
    have ecard := Finset.card_union_of_disjoint edecompdisj
    rw [← edecomp] at ecard
    simp +arith [ecard, e₂]
    clear edecomp edecompdisj ecard
    rw [Finset.card_biUnion]
    · simp
      have fibwise := Finset.sum_fiberwise (G.neighborFinset p) (λ j ↦ @Fin.mk (σ_G hxy).succ (vᵢ 2 y (G.degree j)) (vᵢjlt j))  (λ j ↦ G.degree j)
      simp at fibwise
      have sumbij := Fintype.sum_bijective id Function.bijective_id (λ d ↦ Finset.sum ((G.neighborFinset p).filter (λ j ↦ @Fin.mk (σ_G hxy).succ (vᵢ 2 y (G.degree j)) (vᵢjlt j) = d)) (λ j ↦ G.degree j)) (λ d ↦ (RamseyOld 2 y.succ - d.val) * ((G.neighborFinset p).filter (λ v ↦  G.degree v = vᵢ 2 y d.val)).card)
      simp at sumbij
      rw [sumbij] at fibwise
      · rw [← fibwise]
        simp [β, ← Finset.sum_add_distrib, ← Nat.add_mul]
        conv =>
          lhs
          arg 2
          intro x
          rw [← Nat.sub_add_comm (by trans σ_G hxy; rw [← Nat.lt_add_one_iff]; exact x.prop; simp [σ_G])]
          simp
        rw [← Finset.mul_sum, Nat.add_comm _ ((vᵢ 2 y i.val)^2), ← tsub_eq_iff_eq_add_of_le, ← Nat.sub_mul, Nat.pow_two]
        · congr
          simp [β] at βsum_eq_card
          simp [← βsum_eq_card]
          assumption
        · apply Nat.mul_le_mul_right
          trans σ_G hxy
          · rw [← Nat.lt_add_one_iff]
            exact i.prop
          · simp [σ_G]
      · intros d
        have innersumbij := @Finset.sum_bijective _ _ _ _  ((G.neighborFinset p).filter (λ j ↦ @Fin.mk (σ_G hxy).succ (vᵢ 2 y (G.degree j)) (vᵢjlt j) = d)) ((G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ 2 y d)) (λ j ↦ G.degree j) (λ j ↦ (RamseyOld 2 y.succ) - d.val) id Function.bijective_id (by simp [Fin.ext_iff, ← vᵢ_deg_swap]) (by simp [Fin.ext_iff, ← vᵢ_deg_swap])
        simp [Nat.mul_comm] at innersumbij
        exact innersumbij
    · simp [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_iff_inter_eq_empty, Finset.eq_empty_iff_forall_notMem]
      intros u pu v pv uneqp e eincu eincv
      have uv := G.adj_of_mem_incidenceSet uneqp eincu eincv
      cases (G.R3y_neighbor_Ind hxy p).isIndepSet (by simpa) (by simpa) uneqp uv
  have ele : ∀ p ∈ (@Finset.univ (Fin N.succ) _), e 3 y (N - G.degree p).pred + vᵢ 2 y (y - G.degree p) ^ 2 + (y - G.degree p) * ∑ j : Fin (σ_G hxy).succ, β p ↑j ≤ #G.edgeFinset + ∑ j : Fin (σ_G hxy).succ, ↑j * β p ↑j := by
    intro p _
    have pdegle := (Lemma₂ G p hxy).left
    simp [RamseyOld₂] at pdegle
    have ilt : y - G.degree p < (σ_G hxy).succ := by
      apply Nat.lt_of_le_sub_one (Nat.succ_pos _)
      simp [σ_G, RamseyOld₂]
      rw [← Nat.sub_add_comm (Nat.le_trans (G.minDegree_le_degree p) pdegle), Nat.add_sub_assoc (G.minDegree_le_degree p)]
      simp
    let i : Fin (σ_G hxy).succ := ⟨y - G.degree p, ilt⟩
    have pvᵢ : G.degree p = vᵢ 2 y i.val := by simp [vᵢ, i, RamseyOld₂, Nat.sub_sub_self pdegle]
    simp +arith only [ecount p pvᵢ, i]
    exact (e₂_ge_e p hxy).le
  have allpoints := Finset.sum_le_sum ele
  simp [Finset.sum_add_distrib, ← βsum_eq_card]  at allpoints
  rw [Finset.sum_comm] at allpoints
  simp [← Finset.mul_sum] at allpoints
  let B : ℕ → ℕ := λ j ↦ (Finset.univ.filter (λ v ↦ G.degree v = vᵢ 2 y j)).card
  have βsum_eq_B : ∀ (j : Fin (σ_G hxy).succ), Finset.sum Finset.univ (λ v ↦ β v ↑j) = (vᵢ 2 y j) * (B ↑j) := by
    intro j
    have dblcnt := @Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (Fin N.succ) (Fin N.succ) G.Adj Finset.univ (Finset.univ.filter (λ v ↦ G.degree v = vᵢ 2 y j)) _
    simp [bipartiteAbove, bipartiteBelow] at dblcnt
    simp [β, G.neighborFinset_eq_filter]
    conv =>
      lhs
      arg 2
      intro x
      arg 1
      rw [Finset.filter_comm]
    rw [dblcnt]
    trans Finset.sum (Finset.univ.filter (λ v ↦ G.degree v = vᵢ 2 y ↑j)) (vᵢ 2 y ↑j)
    · apply Finset.sum_bijective id Function.bijective_id
      · simp
      · simp [vᵢ]
        intro v vdeg
        rw [← vdeg, ← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
        congr
        ext u
        apply Iff.intro <;> apply G.symm
    · simp [B, RamseyOld₂, vᵢ, Nat.mul_comm]
  simp [βsum_eq_B, B, vᵢ, RamseyOld₂] at allpoints
  have fibwise_lhs :=  @Fintype.sum_fiberwise ℕ (Fin (σ_G hxy).succ) (Fin N.succ) _ _ _ _ (λ v ↦ ⟨vᵢ 2 y (G.degree v), vᵢjlt v⟩) (λ d ↦ (y - (G.degree d)) * (G.degree d))
  have fibwise_rhs := @Finset.sum_bijective (Fin (σ_G hxy).succ) (Fin (σ_G hxy).succ) ℕ _ Finset.univ Finset.univ (λ d ↦ Finset.sum Finset.univ (λ (v : { i // ⟨vᵢ 2 y (G.degree i), by simp [vᵢjlt]⟩ = d }) ↦ (y - G.degree v.val) * (G.degree v.val))) (λ d ↦ d.val * ((y - d.val) * (Finset.univ.filter (λ v ↦ G.degree v = y - d.val)).card)) id Function.bijective_id (by simp)
  simp at fibwise_lhs fibwise_rhs
  rw [← fibwise_lhs, fibwise_rhs, Nat.add_le_add_iff_right] at allpoints
  · rw [← Finset.sum_add_distrib] at allpoints
    have yafibwise := @Fintype.sum_fiberwise ℕ (Fin (σ_G hxy).succ) (Fin N.succ) _ _ _ _ (λ v ↦ ⟨vᵢ 2 y (G.degree v), vᵢjlt v⟩) (λ v ↦ e 3 y (N - G.degree v - 1) + (y - (y - G.degree v))^2)
    have yafibbij := @Finset.sum_bijective (Fin (σ_G hxy).succ) (Fin (σ_G hxy).succ) ℕ _ Finset.univ Finset.univ (λ d ↦ Finset.sum Finset.univ (λ (v : { i // ⟨vᵢ 2 y (G.degree i), by simp [vᵢjlt]⟩ = d }) ↦ e 3 y (N - G.degree v.val - 1) + (y - (y - G.degree v.val))^2)) (λ d ↦ (e 3 y (N - vᵢ 2 y d.val - 1) + (vᵢ 2 y d.val)^2) * (G.sᵢ 2 y d.val)) id Function.bijective_id (by simp)
    rw [yafibbij] at yafibwise
    · rw [← yafibwise] at allpoints
      simp [Finset.sum_range] at allpoints ⊢
      exact allpoints
    · simp
      intro i
      have ile := i.prop
      simp at ile
      rw [@Fintype.sum_bijective ↑{ w // ⟨vᵢ 2 y (G.degree w), _⟩ = i } ↑{ w // ⟨vᵢ 2 y (G.degree w), _⟩ = i } ℕ _ _ _ id Function.bijective_id (λ v ↦ e 3 y (N - G.degree v.val - 1) + (y - (y - G.degree v.val))^2) (λ v ↦ e 3 y (N - vᵢ 2 y i.val - 1) + (y - (y - vᵢ 2 y i.val))^2)]
      · simp [Finset.sum_const, Nat.sub_sub_self (by simp [vᵢ, RamseyOld₂] : vᵢ 2 y i.val ≤ y), Nat.mul_comm]
        left
        simp [sᵢ]
        apply Finset.card_nbij (λ i ↦ i.val) <;> simp [Set.InjOn, Set.SurjOn, Subtype.val_inj, Fin.ext_iff, vᵢ_deg_swap]
      · simp
        intro v veq
        simp [Fin.ext_iff, vᵢ, Nat.sub_eq_iff_eq_add (Lemma₂ G v hxy).left] at veq
        rw [Nat.add_comm i.val, ← Nat.sub_eq_iff_eq_add] at veq
        · change vᵢ 2 y i.val = G.degree v at veq
          simp [← veq]
        · trans σ_G hxy
          · exact ile
          · simp [σ_G]
  · intro i
    rw [@Fintype.sum_bijective ↑{ v // ⟨vᵢ 2 y (G.degree v), _⟩ = i } ↑{ v // ⟨vᵢ 2 y (G.degree v), _⟩ = i } ℕ _ _ _ id Function.bijective_id (λ v ↦ (y - G.degree v.val) * (G.degree v.val)) (λ v ↦ i.val * (y - i.val))]
    have ile := i.prop
    simp at ile
    · simp [Finset.sum_const, Nat.mul_comm _ (i.val * (y - i.val)), Nat.mul_assoc]
      left
      left
      apply Finset.card_nbij (λ i ↦ i.val) <;> simp [Set.InjOn, Set.SurjOn, Subtype.val_inj, Fin.ext_iff, vᵢ_deg_swap] <;> simp [vᵢ, RamseyOld₂]
    · intro v
      have veq := v.prop
      simp [Fin.ext_iff, vᵢ, RamseyOld₂] at veq
      have vle := (Lemma₂ G v.val hxy).left
      simp [RamseyOld₂] at vle
      rw [← veq, Nat.sub_sub_self vle]

end Nonempty

end SimpleGraph
