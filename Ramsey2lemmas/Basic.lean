import Mathlib.Data.Rat.Init
import Lean.Parser.Tactic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Nat.Lattice

namespace SimpleGraph

------------------------------------------------ GraphRamsey From Previous Project
def RamseyGraphProp (N s t : ℕ) : Prop := (∀ (G : SimpleGraph (Fin N)) [DecidableRel G.Adj], (∃ S, G.IsNClique s S) ∨ (∃ T, Gᶜ.IsNClique t T))

noncomputable def GraphRamsey (s t : ℕ) : ℕ := sInf { N : ℕ | RamseyGraphProp N s t }

lemma RamseyGraphMonotone : ∀ {N s t}, RamseyGraphProp N s t → ∀ {M}, N ≤ M → RamseyGraphProp M s t := by
  unfold RamseyGraphProp
  intros N s t R M NleqM G _
  let subAdj : Fin N → Fin N → Prop := λ u v ↦ G.Adj (Fin.castLE NleqM u) (Fin.castLE NleqM v)
  have subAdjSym : Symmetric subAdj := by
    unfold Symmetric
    simp only [subAdj]
    intros _ _ xAdjy
    simp only [Adj.symm xAdjy]
  have subAdjLoopless : Irreflexive subAdj := by
    unfold Irreflexive
    simp [subAdj]
  let G' : SimpleGraph (Fin N) := { Adj := subAdj, symm := subAdjSym, loopless := subAdjLoopless }
  rcases R G' with ⟨S, SProp⟩ | ⟨S, SProp⟩
  left; swap; right
  all_goals{
    use S.map (Fin.castLEEmb NleqM)
    simp [isNClique_iff, IsClique, Set.Pairwise] at SProp ⊢
    simp [SProp.right]
    intros x _ y _ _
    have xNeqy : x ≠ y := by intro; simp_all
    simp_all
    tauto
  }

theorem GraphRamsey2 : ∀ k : ℕ, GraphRamsey 2 k.succ = k.succ := by
  intros k
  unfold GraphRamsey

  have RamseyGraph2Monotone : ∀ M₁ M₂, M₁ ≤ M₂ → M₁ ∈ { N : ℕ | RamseyGraphProp N 2 k.succ } → M₂ ∈ { N : ℕ | RamseyGraphProp N 2 k.succ }
  intros M₁ M₂ M₁leM₂
  simp
  intro M₁Ramsey
  apply RamseyGraphMonotone M₁Ramsey M₁leM₂
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  simp
  apply And.intro
  unfold RamseyGraphProp
  intros G _
  simp [SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  rcases Finset.eq_empty_or_nonempty (G.edgeFinset) with GEmp| ⟨⟨x,y⟩, xyInG⟩

  · rw [Finset.eq_empty_iff_forall_not_mem] at GEmp
    right
    use Finset.univ
    simp_all
    intros x y _
    let e : Sym2 (Fin (k + 1)) := s(x, y)
    have tmp := GEmp e
    tauto

  · left
    use {x,y}
    simp[Finset.card_eq_two]
    simp_all
    apply And.intro
    swap
    · use x, y
      simp
      intro h
      simp_all
    · intros
      simp [xyInG, SimpleGraph.Adj.symm]

  simp [RamseyGraphProp, SimpleGraph.isNClique_iff, SimpleGraph.IsClique, Set.Pairwise]
  use (⊥ : SimpleGraph (Fin k))
  simp
  apply And.intro <;>
  intros S HS
  by_contra H
  rw [Finset.card_eq_two] at H
  obtain ⟨x, y, hxy⟩ := H
  simp_all

  have tmp := card_finset_fin_le S
  rw [HS] at tmp
  simp at tmp

  assumption
------------------------------------------------ RamseyOld
section FintypeVGraph
variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

-- Define the Independence number for a SimpleGraph G
noncomputable abbrev indNum : ℕ := Gᶜ.cliqueNum

-- an (x,y)-graph on n vertices iff does not have clique of size x or independet set of size y
def isXYGraph : Prop := G.cliqueNum < x ∧ G.indNum < y

noncomputable def RamseyOld : ℕ  :=  sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)) (_ : DecidableRel G.Adj), G.isXYGraph x y}

theorem Lemma₁ : G.isXYGraph x y ↔ Gᶜ.isXYGraph y x := by
  simp [isXYGraph, indNum]
  tauto

variable [Fintype V]
lemma cardLERamseyOld [DecidableEq V] : G.isXYGraph x y → Fintype.card V ≤ RamseyOld x y := by
  intro
  simp [RamseyOld]
  apply le_csSup
  sorry

------------------------------------------------ RamseyOld <-> GraphRamsey
variable {G}
lemma exists_IsNClique_of_lt_cliqueNum  {n : ℕ} (h : n < G.cliqueNum) :
{n | ∃ s, G.IsNClique n s}.Nonempty → ∃ S : Finset V, G.IsNClique n S := by
    intro h'
    simp [cliqueNum] at h
    rw [lt_csSup_iff] at h
    obtain ⟨n', ⟨s', s'prop⟩, nltn'⟩ := h
    · simp [isNClique_iff] at s'prop
      rw [← s'prop.right] at nltn'
      obtain ⟨t, tprop⟩ := Finset.exists_subset_card_eq (le_of_lt nltn')
      use t
      simp [← tprop.right, isNClique_iff]
      have _ := @IsClique.subset V G s' t tprop.left s'prop.left
      assumption
    · use Fintype.card V
      rintro y ⟨s, syc⟩
      rw [isNClique_iff] at syc
      rw [← syc.right]
      exact Finset.card_le_card (Finset.subset_univ s)
    · exact h'

lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card V
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

lemma cliqueNum2CliqueFree: G.cliqueNum < x ↔ G.CliqueFree x := by
  simp [CliqueFree, isNClique_iff]
  apply Iff.intro
  · intros H_cliqueNum S SIsClique
    have tmp : S.card ≤ G.cliqueNum := @IsClique.card_le_cliqueNum  _ G _ S SIsClique
    by_contra
    linarith
  · intro NotXClique
    obtain ⟨S, SMaxClique⟩ := G.maximumClique_exists
    have SCardEqCN := maximumClique_card_eq_cliqueNum S SMaxClique
    simp [isMaximumClique_iff] at SMaxClique
    have SCardNEx := NotXClique S SMaxClique.left
    rw [SCardEqCN] at SCardNEx
    rcases Nat.lt_or_gt_of_ne (Ne.symm SCardNEx) with h | h
--TODO: modularize nonempty as lemma
    · have nonempty : {n | ∃ s, G.IsNClique n s}.Nonempty := by
        unfold Set.Nonempty
        use S.card; use S
        simp[isNClique_iff]
        exact SMaxClique.left
      obtain ⟨T, TClique⟩ := exists_IsNClique_of_lt_cliqueNum h nonempty
      simp [G.isNClique_iff] at TClique
      have contra := NotXClique T TClique.left
      simp_all
    · assumption

theorem noXYGraphIffRamseyGraphProp (N: ℕ): (∀(G : SimpleGraph (Fin N)) [DecidableRel G.Adj], ¬ G.isXYGraph x y) ↔ RamseyGraphProp N x y := by
  simp [isXYGraph, RamseyGraphProp, indNum]
  apply Iff.intro <;> intros H G
  · have cliqueNumProp := H G
    by_contra RamseyProp
    by_cases H : G.cliqueNum < x
    · have H₁ := not_lt_of_le (cliqueNumProp H)
      simp [cliqueNum2CliqueFree] at H H₁
      simp_all [CliqueFree]
    · simp [cliqueNum2CliqueFree] at H
      simp_all [CliqueFree]
  · intro cliqueNumProp
    obtain ⟨S,SClique⟩ | ⟨T, TClique⟩ := H G
    · rw [cliqueNum2CliqueFree] at cliqueNumProp
      simp_all [CliqueFree]
    · by_contra H
      simp [cliqueNum2CliqueFree] at H
      simp_all [CliqueFree]

--TODO: prove mono_RamseyOld
theorem GraphRamsey2RamseOld : GraphRamsey x y = RamseyOld x y + 1 := by
  simp [GraphRamsey]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  . simp_all
    apply And.intro
    · simp [← noXYGraphIffRamseyGraphProp]
      intro G _
      by_contra H
      sorry
    · sorry

variable (i : ℕ) (G) [DecidableRel G.Adj]
noncomputable abbrev v_i : ℕ := RamseyOld x y.succ - i --TODO: add succ here ??

noncomputable abbrev s_i : ℕ := (Finset.univ).filter (λ v ↦ G.degree v = v_i x y i) |>.card
noncomputable abbrev t_i (p : V): ℕ := (G.neighborFinset p).filter (λ v ↦ G.degree v = v_i x y i) |>.card

variable {G x y}
noncomputable def σ_G (_ : G.isXYGraph x.succ y.succ) : ℕ := RamseyOld x y.succ - G.minDegree

lemma sum_degree_eq_sum_over_degrees :
  ∑ v : V, G.degree v =
    ∑ d in Finset.image (λ v => G.degree v) Finset.univ, d * ((Finset.univ).filter (λ v => G.degree v = d)).card := by

    have h_sigma : (∑ v: V, G.degree v) =
    ∑ p in Finset.sigma (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v =>  G.degree v = d)), G.degree p.2 := by
      apply Finset.sum_bij (λ v hv => ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]

    rw [h_sigma]

    have h_inner_sum : ∀ d ∈ (Finset.image (λ v => G.degree v) Finset.univ),
    (∑ v in (Finset.univ.filter (λ v => G.degree v = d)), G.degree v) =
    d * ((Finset.univ).filter (λ v => G.degree v = d)).card := by
      intros d hd
      have h : ∀ v ∈ (Finset.univ.filter (λ v => G.degree v = d)), G.degree v = d := by
        intros v hv
        rw [Finset.mem_filter] at hv
        rcases hv with ⟨hv1, hv2⟩
        rw [hv2]
      rw [Finset.sum_const_nat h]
      apply mul_comm

    suffices:
      (∑ p in Finset.sigma  (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v => G.degree v = d)), G.degree p.2) =
      (∑ d in (Finset.image (λ v => G.degree v) Finset.univ), ∑ v in Finset.univ.filter (λ v =>  G.degree v = d), G.degree v)
    rw[this]
    apply Finset.sum_congr rfl h_inner_sum
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
-- set_option pp.explicit true
lemma oneLeCN: 1 ≤ G.cliqueNum := by
  apply le_csSup fintype_cliqueNum_bddAbove
  simp
  tauto

lemma indNumMono : (H₁ G p).indNum ≤ G.indNum := by
  simp [indNum, cliqueNum]
  apply csSup_le_csSup'
  · exact fintype_cliqueNum_bddAbove
  · rintro n ⟨S, SProp⟩
    simp
    use S.map (Function.Embedding.subtype _)
    simp [isNClique_iff,IsClique] at SProp ⊢
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
    suffices : ∃ s, G.IsNClique n.succ s
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
  -- apply And.intro
  apply And.intro
  · have H₁isXYGraph: (H₁ G p).isXYGraph x y.succ := by
      have indNum_mono := indNumMono G p
      have cliqueNum_mono := cliqueNumMono G p
      simp [isXYGraph] at xyGraphProp ⊢
      simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at xyGraphProp
      simp [lt_of_le_of_lt indNum_mono xyGraphProp.right]
      linarith

    have tmp := (cardLERamseyOld (H₁ G p) x y.succ H₁isXYGraph)
    rw [card_neighborSet_eq_degree] at tmp
    exact tmp

  · have H₁isXYGraph_C : (H₁ Gᶜ p)ᶜ.isXYGraph x.succ y := by
      have indNum_mono := indNumMono Gᶜ p
      have cliqueNum_mono := cliqueNumMono Gᶜ p
      rw [Lemma₁] at xyGraphProp ⊢
      simp [isXYGraph] at xyGraphProp ⊢
      simp[← Nat.sub_lt_sub_iff_right (oneLeCN Gᶜ)] at xyGraphProp
      simp [lt_of_le_of_lt cliqueNum_mono xyGraphProp.left]
      linarith

    simp [isXYGraph] at H₁isXYGraph_C
    have tmp := (cardLERamseyOld (H₁ Gᶜ p)ᶜ x.succ y H₁isXYGraph_C)
    rw [card_neighborSet_eq_degree] at tmp
    have _ := G.degree_compl
    simp_all
    linarith
theorem tmp: ((⊥ : (SimpleGraph (Fin (2).succ)) ) = (⊥ :(SimpleGraph (Fin (2 + 1))) )) ↔ true := by
apply Iff.intro
intro
rfl
intro
rfl


lemma G_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : Fin N.succ, G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.s_i x y j * v_i x y j := by
  rw [sum_degree_eq_sum_over_degrees]

  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a
    have _ := G.minDegree_le_degree a
    omega
  · simp
    intros a₁ a₂ h
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb
    rw [Nat.lt_succ_iff] at hb

    obtain ⟨a, ha⟩ : ∃ a : Fin N.succ, G.degree a = RamseyOld x (y + 1) - b := by sorry
--       have tmp :  RamseyOld x (y + 1) - b ∈ Set.range (λ v : Fin N.succ ↦ G.degree v) := by

-- ]        sorry
--       rwa [Set.mem_range] at tmp
      -- by_contra!
      -- have tmp : ∀ (a : Fin N.succ), G.degree a < RamseyOld x (y + 1) - b ∨ G.degree a > RamseyOld x (y + 1) - b := by
      --   intro a
      --   specialize this a
      --   rw [ne_iff_lt_or_gt] at this
      --   exact this
      -- rcases tmp

    use a
    rw [ha, Nat.sub_sub_self]
    omega
  · simp [s_i, v_i]
    intros a
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    simp[tmp, mul_comm]

  -- let I_H1 := (G.neighborFinset p).map ⟨Subtype.val, Subtype.val_injective⟩
variable {G}

theorem Prop₁ (hxy : G.isXYGraph x.succ y.succ):
N.succ ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 - (σ_G hxy) ∧ (σ_G hxy) ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 -  N.succ := by
  obtain ⟨p, hp⟩ := G.exists_minimal_degree_vertex
  -- let ⟨p, hp⟩ : ∃ p : Fin N.succ, G.degree p = v := by
  --   have _: {x | ∃ p, degree G p = x}.Nonempty := by simp [Set.Nonempty]; let p : Fin N.succ := 0; use G.degree p, p
  --   have H : sInf {x | ∃ p, degree G p = x} ∈ {x | ∃ p, degree G p = x} := by apply Nat.sInf_mem; assumption
  --   simp_all
  have ⟨ha, hb⟩ := (Lemma₂ G p hxy)
  simp[σ_G]
  apply And.intro
  -- have temp : (RamseyOld x y.succ - G.minDegree) ≤ RamseyOld x y.succ + RamseyOld x.succ y + 1 := by simp; linarith
  rw[Nat.le_sub_iff_add_le (by simp; linarith)]
  have vLERamseyOld : G.minDegree ≤ RamseyOld x y.succ := by rw [← hp] at ha; exact ha
  rw [← Nat.add_sub_assoc vLERamseyOld]
  simp_all
  linarith

  suffices :  0 ≤ (RamseyOld x.succ y + G.minDegree - N)
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
  rw [← hp] at hb; simp [hb]

variable (x y i)

theorem Prop₂ (hxy : G.isXYGraph x.succ y.succ) (hp: G.degree p = v_i x y i) : 2 * (↑(e₂ G p  - e₁ G p) : ℤ ) =
RamseyOld x y.succ * (N.succ - 2 * RamseyOld x y.succ + 2 * i) + ∑ j in Finset.range (σ_G hxy).succ, j * (2 * t_i G x y j p - (s_i G x y j)) := by
  let e := G.edgeFinset.card
  let lhs := ∑ j in Finset.range (σ_G hxy).succ, (t_i G x y j p) * (v_i x y j)
  let rhs := ∑ j in Finset.range (σ_G hxy).succ, (s_i G x y j) * (v_i x y j)

  have count₁ : e = lhs - e₁ G p + e₂ G p := by
    sorry

  have count₂ : 2 * e = rhs := by
    -- suffices : 2 * e = rhs
    simp only[e, ← sum_degrees_eq_twice_card_edges]
    apply G_degreeCount_eq

  rw [count₁] at count₂

  have count₂ : 2 * (G.e₂ p - G.e₁ p) = rhs - 2 * lhs := by
    have tmp : G.e₁ p ≤ lhs := by sorry
    rw [← Nat.sub_add_comm tmp] at count₂
    omega
  zify at count₂ -- Pretty difficult to think of the correct type coercion
  conv at count₂ =>
    rhs
    unfold lhs rhs
    rw [Finset.mul_sum]
    rw [Nat.cast_sub (by sorry), Nat.cast_sum, Nat.cast_sum]
    simp[v_i]

  --hard to work with under conv, easier to show bijective
  have part₁ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * (↑(RamseyOld x (y + 1) - x_1):ℤ)
  =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (↑(G.s_i x y x_1) * (↑(RamseyOld x (y + 1)): ℤ) - ↑(G.s_i x y x_1) * x_1) := by
    apply Finset.sum_bij (λ a ha ↦ a) <;> simp
    intros a ha
    rw[Nat.cast_sub (by sorry)]
    linarith
  rw[Finset.sum_sub_distrib] at part₁
  rw [← Finset.sum_mul] at part₁
  have tmp₁ : (∑ i ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y i):ℤ) = N.succ := by sorry
  rw [tmp₁] at part₁

    --hard to work with under conv, easier to show bijective
  have part₂ :  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * (↑(G.t_i x y x_1 p) * ↑(RamseyOld x (y + 1) - x_1):ℤ)
  =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.t_i x y x_1 p) * (↑(RamseyOld x (y + 1)): ℤ) - 2 * ↑(G.t_i x y x_1 p) * x_1) := by
    apply Finset.sum_bij (λ a ha ↦ a) <;> simp
    intros a ha
    rw[Nat.cast_sub (by sorry)]
    linarith
  rw [Finset.sum_sub_distrib] at part₂
  rw [← Finset.sum_mul] at part₂
  have tmp₂ : (∑ i ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y i p): ℤ) = 2 * v_i x y i := by sorry
  rw [tmp₂] at part₂

  rw [part₁, part₂] at count₂
  rw [count₂]
  simp
  rw [sub_sub_sub_comm]
  rw [sub_sub_eq_add_sub, add_sub_assoc]
  rw [← Finset.sum_sub_distrib]

  have _ :  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.t_i x y x_1 p) * ↑x_1 - ↑(G.s_i x y x_1) * ↑x_1) = ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑x_1 * ↑(2 * G.t_i x y x_1 p - G.s_i x y x_1) :=  by
    apply Finset.sum_bij (λ a ha ↦ a) <;> simp
    intros a ha
    zify
    rw[Nat.cast_sub (by sorry), Nat.cast_sub (by sorry)]
    rw [mul_sub,  Nat.cast_mul]
    ring


  -- simp [← Int.sub_sub]
  -- suffices : ↑N.succ * ↑(RamseyOld x (y + 1)) - (2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1))) = ↑(RamseyOld x (y + 1)) * (N.succ - 2 * ↑(v_i x y i))
  -- simp [this]
  -- have _  : (↑N + 1) * ↑(RamseyOld x (y + 1)) - ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * ↑x_1 + ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y x_1 p) * ↑x_1 - 2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1))
  --   = (↑N + 1) * ↑(RamseyOld x (y + 1)) - 2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1)) + ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y x_1 p) * ↑x_1 - ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * ↑x_1 := by
  --   norm_cast
  --   have _ : (N + 1) * RamseyOld x (y + 1) ≥ 2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1)) := by sorry
  --   have _ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y x_1 p) * ↑x_1 ≥ ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * ↑x_1 := by sorry
  --   linarith

-- calc   (↑N + 1) * ↑(RamseyOld x (y + 1)) - ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * ↑x_1 + ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y x_1 p) * ↑x_1 - 2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1))
--     = (↑N + 1) * ↑(RamseyOld x (y + 1))  - 2 * ↑(v_i x y i) * ↑(RamseyOld x (y + 1)) + ∑ x_1 ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.t_i x y x_1 p) * ↑x_1 - ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.s_i x y x_1) * ↑x_1 := by rfl
--    _ = ↑(RamseyOld x (y + 1)) * ((↑N + 1) - 2 * ↑(v_i x y i))  := by rfl
--    _ =   ↑(RamseyOld x (y + 1)) * (↑N + 1 - 2 * ↑(RamseyOld x (y + 1)) + 2 * ↑i) +
--     ∑ x_1 ∈ Finset.range (σ_G hxy), (↑x_1 + 1) * ↑(2 * G.t_i x y (x_1 + 1) p - G.s_i x y x_1) := by sorry


theorem Corollary₂  (hxy : G.isXYGraph 3 y.succ) (hp: G.degree p = v_i 2 y i) :
  e₂ G p = y * (N.succ / 2 - y + i) + ∑ j in Finset.range (σ_G hxy), j.succ * (t_i G 2 y j.succ p - (s_i G 2 y j) / 2) := by
  have Prop₂ := Prop₂ 2 y p i hxy hp
  suffices tmp: G.e₁ p = 0 ∧ RamseyOld 2 y.succ = y
  rw [tmp.left, tmp.right] at Prop₂
  simp_all
  apply And.intro
  · simp [Finset.filter_eq_empty_iff]
    by_contra H
    simp at H
    obtain ⟨⟨u, v⟩, uvProp⟩ := H
    simp [isXYGraph] at hxy
    suffices : (G.H₁ p).cliqueNum < 2

    simp [cliqueNum2CliqueFree, CliqueFree, isNClique_iff] at this
    have contra := this {u,v}
    simp [IsClique] at contra uvProp
    simp [uvProp] at contra
    rw [Finset.card_insert_of_not_mem] at contra
    trivial

    by_contra
    simp_all

    have H₁CliqueNum_UB := cliqueNumMono G p
    simp[← Nat.sub_lt_sub_iff_right (oneLeCN G)] at hxy
    linarith

  · have tmp := GraphRamsey2 y
    simp [GraphRamsey2RamseOld] at tmp
    exact tmp

theorem Prop₃ (hxy: G.isXYGraph 3 y) (h: ∃ u v: Fin N.succ, G.Adj u v ∧ G.degree u = (v_i 3 y i) ∧ G.degree v = (v_i 3 y i)):
  let p := Exists.choose h -- use classical.choose, is this bad?
  haveI : DecidableRel (H₂ G p).Adj := by apply  instDecidableComapAdj
  let e₂ := (H₂ G p).edgeFinset.card
  e₂ ≤ (y - 1) * (N.succ / 2 - y + 1 + i):= by
  sorry

noncomputable def e_x_y_n (x y N : ℕ) : ℕ := sInf {n : ℕ | ∃ (G : SimpleGraph (Fin N.succ)) (_ : DecidableRel G.Adj), G.isXYGraph x y ∧ G.edgeFinset.card = n}

theorem Prop₄ (hxy: G.isXYGraph 3 y):
  let e := G.edgeFinset.card
  let s_i := λ i ↦ (Finset.univ : Finset (Fin N.succ)).filter (λ v ↦ G.degree v = v_i x y i) |>.card
  let vᵢ := v_i 3 y i
  N.succ * e ≥ (∑ i in Finset.range (σ_G hxy).succ, e_x_y_n 3 (y-1) (N.succ - vᵢ - 1) + vᵢ^2) * s_i i:= by
  sorry
