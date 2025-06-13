import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic

import Ramsey2lemmas.Sym2

import FormalRamsey.Ramsey2Color

namespace SimpleGraph

section FintypeVGraph
variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

-- Define the Independence number for a SimpleGraph G
noncomputable abbrev indNum : ℕ := Gᶜ.cliqueNum

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

lemma Iso.IsNClique (iso : G ≃g G') : G.IsNClique n s ↔ G'.IsNClique n (s.map iso.toEquiv) := by simp [isNClique_iff, iso.IsClique]

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

def Iso.compl (iso : G ≃g G') : Gᶜ ≃g G'ᶜ := by
  use iso
  intro u v
  simp [not_iff_not, ← iso.map_rel_iff']

lemma Iso.indNum (iso : G ≃g G') : G.indNum = G'.indNum := by simp [SimpleGraph.indNum, (iso.compl).cliqueNum]

end Iso

-- an (x,y)-graph on n vertices iff does not have clique of size x or independet set of size y
def isXYGraph : Prop := G.cliqueNum < x ∧ G.indNum < y

noncomputable def RamseyOld : ℕ  :=  sSup {N : ℕ | ∃ (G : SimpleGraph (Fin N)) (_ : DecidableRel G.Adj), G.isXYGraph x y}

theorem Lemma₁ : G.isXYGraph x y ↔ Gᶜ.isXYGraph y x := by
  simp [isXYGraph, indNum]
  tauto

variable [Fintype V]

lemma exists_isNClique_of_le_cliqueNum  {n : ℕ} (h : n ≤ G.cliqueNum) : ∃ S : Finset V, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma exists_isNIndset_of_le_indNum  {n : ℕ} (h : n ≤ G.indNum) : ∃ S : Finset V, Gᶜ.IsNClique n S := by
  rcases Gᶜ.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

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
      simpa [← (G.overFinIso rfl).cliqueNum, ← (G.overFinIso rfl).indNum]

------------------------------------------------ RamseyOld <-> GraphRamsey
variable {G}

lemma fintype_cliqueNum_bddAbove : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card V
  rintro y ⟨s, syc⟩
  rw [isNClique_iff] at syc
  rw [← syc.right]
  exact Finset.card_le_card (Finset.subset_univ s)

--TODO: prove mono_RamseyOld
theorem GraphRamsey2RamseyOld : GraphRamsey x y = RamseyOld x y + 1 := by
  simp [GraphRamsey]
  rw [Nat.sInf_upward_closed_eq_succ_iff]
  . simp_all
    apply And.intro
    · simp [← noXYGraphIffRamseyGraphProp]
      intro G _
      by_contra H
      sorry
    · sorry
  · simp
    intro M N MleqN MRamsey
    exact RamseyGraphMonotone MRamsey MleqN

variable (i : ℕ) (G) [DecidableRel G.Adj]

noncomputable abbrev vᵢ : ℤ := RamseyOld x y.succ - i

noncomputable abbrev sᵢ : ℕ := (Finset.univ).filter (λ v ↦ G.degree v = vᵢ x y i) |>.card

noncomputable abbrev tᵢ (p : V): ℕ := (G.neighborFinset p).filter (λ v ↦ G.degree v = vᵢ x y i) |>.card

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

    suffices
      (∑ p in Finset.sigma  (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v => G.degree v = d)), G.degree p.2) =
      (∑ d in (Finset.image (λ v => G.degree v) Finset.univ), ∑ v in Finset.univ.filter (λ v =>  G.degree v = d), G.degree v) by
      rw [this]
      apply Finset.sum_congr rfl h_inner_sum
    simp [Finset.sum_sigma']

lemma num_of_vertices_eq_sum_over_degrees : Fintype.card V =
  ∑ d in Finset.image (λ v => G.degree v) Finset.univ, ((Finset.univ).filter (λ v => G.degree v = d)).card := by
  transitivity (∑ v: V, 1)
  simp
  have h_sigma : (∑ v: V, 1) =
    ∑ p in Finset.sigma (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v =>  G.degree v = d)), 1 := by
      apply Finset.sum_bij (λ v hv => ⟨G.degree v, v⟩) <;> simp
      intros p _ _ h
      use p.2
      rw [h]
  rw [h_sigma]
  suffices
      (∑ p in Finset.sigma  (Finset.image (λ v => G.degree v) Finset.univ) (λ d => Finset.univ.filter (λ v => G.degree v = d)), 1) =
      (∑ d in (Finset.image (λ v => G.degree v) Finset.univ), ∑ v in Finset.univ.filter (λ v =>  G.degree v = d), 1) by
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

lemma G_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : Fin N.succ, G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.sᵢ x y j * vᵢ x y j := by
  rw [sum_degree_eq_sum_over_degrees]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.sᵢ x y j > 0) , G.sᵢ x y j * vᵢ x y j)
  push_cast
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, vᵢ]
    use a
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ a₂ h
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [vᵢ]
    intros a
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[tmp, mul_comm]
    by_cases aeq0 : G.degree a = 0
    right
    exact aeq0
    left
    simp[sᵢ, vᵢ]
    suffices : (Finset.univ.filter (fun v ↦ G.degree v = G.degree a)) = Finset.univ.filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
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
  · simp[σ_G]
    intro a
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, vᵢ]
    use a
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ a₂ h
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [vᵢ]
    intros a
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[sᵢ, vᵢ]
    suffices : Finset.univ.filter (fun v ↦ G.degree v = G.degree a) = Finset.univ.filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw [tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.sᵢ x y j > 0) (λ j ↦ (G.sᵢ x y j))]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp[sᵢ]
    replace h := Finset.card_eq_zero.mpr h
    exact h.symm

lemma H₁_degreeCount_eq (hxy : G.isXYGraph x.succ y.succ) : ∑ v : ↑(G.neighborFinset p), G.degree v = ∑ j ∈ Finset.range (σ_G hxy).succ, G.tᵢ x y j p * vᵢ x y j := by
  suffices : ∑ v : ↑(G.neighborFinset p), G.degree v = ∑ d in Finset.image (λ v ↦ G.degree v) (G.neighborFinset p), d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card
  rw[this]
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.tᵢ x y j p > 0) , G.tᵢ x y j p * vᵢ x y j)
  push_cast
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intros a ha
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, vᵢ]
    use a
    refine ⟨ha, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ _ a₂ _
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    refine ⟨ha.left, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [vᵢ]
    intros a ha
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[tmp, mul_comm]
    by_cases aeq0 : G.degree a = 0
    right
    exact aeq0
    left
    simp[tᵢ, vᵢ]
    suffices : ((G.neighborFinset p).filter (fun v ↦ G.degree v = G.degree a)) = (G.neighborFinset p).filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.tᵢ x y j p > 0) (λ j ↦ ↑(G.tᵢ x y j p) * vᵢ x y j)]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    left
    assumption

  have h_sigma : (∑ v: (G.neighborFinset p), G.degree v) =
  ∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), G.degree p.2 := by
    apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
    intros a ha
    use a
    intros p _ _ _ _ _
    use p.2
    simp_all

  rw [h_sigma]

  have h_inner_sum : ∀ d ∈ ((G.neighborFinset p).image (λ v ↦ G.degree v)),
  (∑ v in ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v) =
  d * ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)).card := by
    intros d hd
    have h : ∀ v ∈ ((G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree v = d := by
      intros v hv
      rw [Finset.mem_filter] at hv
      rcases hv with ⟨hv1, hv2⟩
      rw [hv2]
    rw [Finset.sum_const_nat h]
    apply mul_comm

  suffices:
    (∑ p in Finset.sigma  ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), G.degree p.2) =
    (∑ d in ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v in (G.neighborFinset p).filter (λ v ↦  G.degree v = d), G.degree v)
  rw[this]
  apply Finset.sum_congr rfl h_inner_sum
  simp [Finset.sum_sigma']

lemma H₁_vertCount_eq (hxy : G.isXYGraph x.succ y.succ) : ↑(Fintype.card ↑(G.neighborSet p)) = (∑ i ∈ Finset.range (σ_G hxy + 1), G.tᵢ x y i p) := by
  transitivity (∑ j ∈ (Finset.range (σ_G hxy).succ).filter (λ j ↦ G.tᵢ x y j p > 0) , G.tᵢ x y j p)
  transitivity (∑ d ∈ (G.neighborFinset p).image (fun v ↦ G.degree v), ((G.neighborFinset p).filter (fun v ↦ G.degree v = d)).card)
  · transitivity (∑ v : (G.neighborSet p), 1)
    simp
    have h_sigma : (∑ v: (G.neighborSet p), 1) =
      ∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦  G.degree v = d)), 1 := by
        apply Finset.sum_bij (λ v hv ↦ ⟨G.degree v, v⟩) <;> simp
        intros a ha
        refine ⟨?_, ha⟩
        use a
        intros p _ _ _ _ _
        use p.2
        simp_all
    rw [h_sigma]
    suffices:
        (∑ p in Finset.sigma ((G.neighborFinset p).image (λ v ↦ G.degree v)) (λ d ↦ (G.neighborFinset p).filter (λ v ↦ G.degree v = d)), 1) =
        (∑ d in ((G.neighborFinset p).image (λ v ↦ G.degree v)), ∑ v in (G.neighborFinset p).filter (λ v ↦  G.degree v = d), 1)
    rw[this]
    apply Finset.sum_congr rfl (by simp)
    simp [Finset.sum_sigma']
  apply Finset.sum_bij (λ d hd ↦ RamseyOld x y.succ - d)
  · simp[σ_G]
    intro a ha
    apply And.intro
    have _ := G.minDegree_le_degree a
    omega
    simp [Finset.Nonempty, vᵢ]
    use a
    refine ⟨ha, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp
    intros a₁ _ a₂ _
    have _ : RamseyOld x (y + 1) ≥ G.degree a₁ := by linarith[(Lemma₂ G a₁ hxy).left]
    have _ : RamseyOld x (y + 1) ≥ G.degree a₂ := by linarith[(Lemma₂ G a₂ hxy).left]
    omega
  · simp[σ_G]
    intros b hb h
    rw [Nat.lt_succ_iff] at hb
    simp[Finset.Nonempty, vᵢ] at h
    obtain ⟨a, ha⟩ := h
    use a
    zify
    refine ⟨ha.left, ?_⟩
    rw [Nat.cast_sub (Lemma₂ G a hxy).left]
    linarith
  · simp [vᵢ]
    intros a ha
    have tmp : RamseyOld x (y + 1) - (RamseyOld x (y + 1) - G.degree a) = G.degree a := by
      rw [Nat.sub_sub_self]
      exact (Lemma₂ G a hxy).left
    zify at tmp
    rw [Nat.cast_sub (by simp)] at tmp
    simp[tᵢ, vᵢ]
    suffices : ((G.neighborFinset p).filter (fun v ↦ G.degree v = G.degree a)) = (G.neighborFinset p).filter (fun v ↦ (↑(G.degree v): ℤ) = ↑(RamseyOld x (y + 1)) - ↑(RamseyOld x (y + 1) - G.degree a))
    rw[this]
    apply Finset.filter_congr
    rw[tmp]
    norm_cast
    tauto
  · rw [Finset.sum_filter (λ j ↦ G.tᵢ x y j p > 0) (λ j ↦ G.tᵢ x y j p)]
    simp[tᵢ, vᵢ]
    apply Finset.sum_bij (λ j _ ↦ j) <;> simp
    intros a ha h
    simp[h]

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
set_option maxHeartbeats 400000

theorem Prop₂ (hxy : G.isXYGraph x.succ y.succ) (hp: G.degree p = vᵢ x y i) : 2 * (((e₂ G p : ℤ)  - e₁ G p)) =
RamseyOld x y.succ * (N.succ - 2 * (RamseyOld x y.succ) + 2 * i) + ∑ j in Finset.range (σ_G hxy).succ, j * (2 * (tᵢ G x y j p) - (sᵢ G x y j : ℤ)) := by
  suffices step1 : Fintype.card (↑G.edgeSet ⊕ ↑(G.induce (G.neighborSet p)).edgeSet) = Fintype.card ({ e : Fin N.succ × Fin N.succ | G.Adj e.fst e.snd ∧ e.fst ∈ G.neighborSet p } ⊕ ↑(G.induce (Gᶜ.neighborSet p)).edgeSet)
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

  · let e := G.edgeFinset.card
    let lhs := ∑ j in Finset.range (σ_G hxy).succ, (tᵢ  G x y j p) * (vᵢ x y j)
    let rhs := ∑ j in Finset.range (σ_G hxy).succ, (sᵢ G x y j) * (vᵢ x y j)
    have count₁ : 2 * e = 2 * (lhs - e₁ G p + e₂ G p) := by
      have : lhs =  ∑ x ∈ G.neighborFinset p, G.degree x  := by
        unfold lhs
        simp [← H₁_degreeCount_eq]
        norm_cast
        rw[Finset.sum_attach (G.neighborFinset p) (λ x ↦ G.degree x)]

      rw[this]
      rw[show ↑(G.e₁ p) = Fintype.card ↑(induce (G.neighborSet p) G).edgeSet by simp [e₁, H₁]]
      rw[show ↑(G.e₂ p) = Fintype.card ↑(induce (Gᶜ.neighborSet p) G).edgeSet by simp [e₂, H₂]]
      rw[show e = Fintype.card ↑G.edgeSet by simp[e]]
      omega
    have count₂ : 2 * e = rhs := by
      norm_cast
      simp only[e, ← sum_degrees_eq_twice_card_edges]
      apply G_degreeCount_eq

    rw [count₁] at count₂

    have count₂ : 2 * (G.e₂ p - G.e₁ p) = ↑rhs - 2 * (↑lhs : ℤ) := by
      omega
    conv at count₂ =>
      rhs
      unfold lhs rhs
      simp[vᵢ]

    have part₁ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.sᵢ x y x_1) * (↑(RamseyOld x (y + 1)) - ↑x_1 : ℤ)
    =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (↑(G.sᵢ x y x_1) * (↑(RamseyOld x (y + 1)): ℤ) - ↑(G.sᵢ x y x_1) * x_1) := by
      apply Finset.sum_bij (λ a ha ↦ a) <;> simp
      intros a ha
      linarith

    rw[Finset.sum_sub_distrib] at part₁
    rw [← Finset.sum_mul] at part₁
    have tmp₁ : N.succ = (∑ i ∈ Finset.range (σ_G hxy + 1), G.sᵢ x y i ) := G_vertCount_eq G hxy
    zify at tmp₁
    rw [tmp₁.symm] at part₁

    have part₂ : 2 * ∑ x_1 ∈ Finset.range (σ_G hxy + 1), ↑(G.tᵢ x y x_1 p) * (↑(RamseyOld x (y + 1)) - ↑x_1 : ℤ)
    =  ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.tᵢ x y x_1 p) * (↑(RamseyOld x (y + 1)): ℤ) - 2 * ↑(G.tᵢ x y x_1 p) * x_1) := by
      rw[Finset.mul_sum]
      apply Finset.sum_bij (λ a ha ↦ a) <;> simp
      intros a ha
      linarith

    rw [Finset.sum_sub_distrib] at part₂
    rw [← Finset.sum_mul] at part₂
    have tmp₂ : (∑ i ∈ Finset.range (σ_G hxy + 1), 2 * ↑(G.tᵢ x y i p): ℤ) = 2 * vᵢ x y i := by
      rw[← hp, ← SimpleGraph.card_neighborSet_eq_degree]
      rw [H₁_vertCount_eq G p hxy]
      simp [Finset.mul_sum]
    rw [tmp₂] at part₂

    rw [part₁, part₂] at count₂
    rw [count₂]
    rw [sub_sub_sub_comm]
    rw [sub_sub_eq_add_sub, add_sub_assoc]
    rw [← Finset.sum_sub_distrib]

    have part₁ : ↑N.succ * ↑(RamseyOld x (y + 1)) - (2 * ↑(vᵢ x y i)) * ↑(RamseyOld x (y + 1)) =  ↑(RamseyOld x y.succ) * (↑N.succ - 2 * ↑(RamseyOld x y.succ) + 2 * ↑i : ℤ) := by
      rw [vᵢ]
      rw [← mul_sub_right_distrib]
      linarith

    have part₂ : ∑ x_1 ∈ Finset.range (σ_G hxy + 1), (2 * ↑(G.tᵢ x y x_1 p) * ↑x_1 - ↑(G.sᵢ x y x_1) * ↑x_1 : ℤ) = ∑ j ∈ Finset.range (σ_G hxy).succ, ↑j * (2 * ↑(G.tᵢ x y j p) - ↑(G.sᵢ x y j): ℤ) := by
      apply Finset.sum_bij (λ a ha ↦ a) <;> simp
      intros a ha
      linarith

    rw [part₂]
    simp at part₁
    rw [part₁]
    simp


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
              tauto
              -- cases pnotadj.left pAdjfst
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

theorem Corollary₂  (hxy : G.isXYGraph 3 y.succ) (hp: G.degree p = vᵢ 2 y i) :
  2 * e₂ G p = ↑y * ((↑N.succ) - 2 * ↑y + 2 * ↑i) + ∑ j in Finset.range (σ_G hxy).succ, (↑j : ℤ) * (2 * ↑ (tᵢ G 2 y j p) - ↑(sᵢ G 2 y j)) := by
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

noncomputable def e_x_y_n (x y N : ℕ) : ℕ := sInf {n : ℕ | ∃ (G : SimpleGraph (Fin N.succ)) (_ : DecidableRel G.Adj), G.isXYGraph x y ∧ G.edgeFinset.card = n}

-- def findᵢ (G : SimpleGraph (Fin N.succ))

theorem Prop₄ (hxy: G.isXYGraph 3 y.succ):
  N.succ * G.edgeFinset.card ≥ (∑ i in Finset.range (σ_G hxy).succ, ((e_x_y_n 3 (y-1) (N.succ - (vᵢ 2 y i) - 1).toNat : ℤ) + (vᵢ 2 y i)^2) * sᵢ G 2 y i) := by
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
