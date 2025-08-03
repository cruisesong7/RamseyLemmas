import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace SimpleGraph

-- NOTE: Missing in Mathlib
theorem IsIndepSet.subset {G : SimpleGraph V} (h : t ⊆ s) : G.IsIndepSet s → G.IsIndepSet t := Set.Pairwise.mono h

-- NOTE: Missing in Mathlib
@[simp]
theorem isNIndepSet_one {G : SimpleGraph V} : G.IsNIndepSet 1 s ↔ ∃ a, s = {a} := by
  simp only [isNIndepSet_iff, Finset.card_eq_one, and_iff_right_iff_imp]; rintro ⟨a, rfl⟩; simp

variable {V : Type*} (G : SimpleGraph V) (x y : ℕ)

namespace Iso

variable {W : Type*} (G' : SimpleGraph W)

lemma IsClique (iso : G ≃g G') : G.IsClique s ↔ G'.IsClique (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsClique, Set.Pairwise]
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

lemma IsIndepSet (iso : G ≃g G') : G.IsIndepSet s ↔ G'.IsIndepSet (iso.toEquiv '' s) := by
  simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  apply Iff.intro <;> intros sprop u uins v vins uneqv
  · simp [← iso.map_rel_iff'] at sprop
    apply sprop <;> assumption
  · rw [← iso.map_rel_iff']
    simp
    apply sprop <;> assumption

lemma IsNClique (iso : G ≃g G') : G.IsNClique n s ↔ G'.IsNClique n (s.map iso.toEquiv) := by simp [isNClique_iff, iso.IsClique]

lemma IsNIndepSet (iso : G ≃g G') : G.IsNIndepSet n s ↔ G'.IsNIndepSet n (s.map iso.toEquiv) := by simp [isNIndepSet_iff, iso.IsIndepSet]

lemma cliqueNum (iso : G ≃g G') : G.cliqueNum = G'.cliqueNum := by
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

lemma indepNum (iso : G ≃g G') : G.indepNum = G'.indepNum := by
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

def compl (iso : G ≃g G') : Gᶜ ≃g G'ᶜ := by
  use iso
  intro u v
  simp [not_iff_not, ← iso.map_rel_iff']

end Iso

section Fintype

lemma fintype_cliqueNum_bddAbove {α : Type} [Fintype α] (G : SimpleGraph α) : BddAbove {n | ∃ s, G.IsNClique n s} := by
  use Fintype.card α
  rintro y ⟨s, syc⟩
  rw [← syc.card_eq]
  apply Finset.card_le_univ

lemma fintype_indepNum_bddAbove {α : Type} [Fintype α] (G : SimpleGraph α) : BddAbove {n | ∃ s, G.IsNIndepSet n s} := by
  use Fintype.card α
  rintro y ⟨s, syc⟩
  rw [← syc.card_eq]
  apply Finset.card_le_univ


lemma exists_isNClique_of_le_cliqueNum {α : Type} [Fintype α] {G : SimpleGraph α} {n : ℕ} (h : n ≤ G.cliqueNum) : ∃ S, G.IsNClique n S := by
  rcases G.exists_isNClique_cliqueNum with ⟨s, sclique⟩
  have nlescard : n ≤ s.card := by simp [h, sclique.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNClique_iff]
  exact sclique.isClique.subset tprop.left

lemma exists_isNIndset_of_le_indepNum {α : Type} [Fintype α] {G : SimpleGraph α} {n : ℕ} (h : n ≤ G.indepNum) : ∃ S, G.IsNIndepSet n S := by
  rcases G.exists_isNIndepSet_indepNum with ⟨s, sindset⟩
  have nlescard : n ≤ s.card := by simp [h, sindset.card_eq]
  obtain ⟨t, tprop⟩ := s.exists_subset_card_eq nlescard
  use t
  simp [← tprop.right, isNIndepSet_iff]
  exact sindset.isIndepSet.subset tprop.left

lemma cliqueNum2CliqueFree {α : Type} [Fintype α] (G : SimpleGraph α) : G.cliqueNum < x ↔ G.CliqueFree x := by
  simp [CliqueFree, isNClique_iff]
  apply Iff.intro
  · intros H_cliqueNum S SIsClique Scard
    simp [← Scard] at H_cliqueNum
    cases (Nat.not_le_of_lt H_cliqueNum) SIsClique.card_le_cliqueNum
  · intro NotXClique
    obtain ⟨S, SMaxClique⟩ := G.maximumClique_exists
    have SCardEqCN := maximumClique_card_eq_cliqueNum S SMaxClique
    simp [isMaximumClique_iff] at SMaxClique
    have SCardNEx := NotXClique S SMaxClique.left
    rw [SCardEqCN] at SCardNEx
    rcases Nat.lt_or_gt_of_ne (Ne.symm SCardNEx) with h | h
    · obtain ⟨T, TClique⟩ := exists_isNClique_of_le_cliqueNum (Nat.le_of_lt h)
      simp [G.isNClique_iff] at TClique
      have contra := NotXClique T TClique.left
      simp_all
    · assumption

end Fintype

namespace Embedding

lemma indepNum_mono {α β : Type} [Fintype α] {G : SimpleGraph α} {G' : SimpleGraph β} (h : G' ↪g G) : G'.indepNum ≤ G.indepNum := by
  simp [indepNum]
  apply csSup_le_csSup'
  · apply fintype_indepNum_bddAbove
  · rintro n ⟨S, SProp⟩
    simp
    use S.map h.toEmbedding
    simp [isNIndepSet_iff, IsIndepSet] at SProp ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ⟨ha_mem, hha⟩⟩
      rcases hb with ⟨hb, ⟨hb_mem, hhb⟩⟩
      simp [Set.Pairwise] at SProp
      simp [← hha, ← hhb]
      apply SProp.left ha_mem hb_mem
      intros hhab
      have contra := congr_arg h hhab
      simp [hha, hhb] at contra
      contradiction
    · exact SProp.right

lemma cliqueNum_mono {α β : Type} [Fintype α] {G : SimpleGraph α} {G' : SimpleGraph β} (h : G' ↪g G) : G'.cliqueNum ≤ G.cliqueNum := by
  simp [cliqueNum]
  apply csSup_le_csSup'
  · apply fintype_cliqueNum_bddAbove
  · rintro n ⟨S, SProp⟩
    simp
    use S.map h.toEmbedding
    simp [isNClique_iff, IsClique] at SProp ⊢
    apply And.intro
    · intros a ha b hb hab
      simp_all
      rcases ha with ⟨ha, ⟨ha_mem, hha⟩⟩
      rcases hb with ⟨hb, ⟨hb_mem, hhb⟩⟩
      simp [Set.Pairwise] at SProp
      simp [← hha, ← hhb]
      apply SProp.left ha_mem hb_mem
      intros hhab
      have contra := congr_arg h hhab
      simp [hha, hhb] at contra
      contradiction
    · exact SProp.right

end Embedding

end SimpleGraph
