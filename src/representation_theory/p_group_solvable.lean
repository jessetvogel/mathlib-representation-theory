import group_theory.solvable group_theory.p_group

open subgroup quotient_group fintype

universe u
variables {G : Type u} [group G]

theorem solvable_of_solvable_quotient_center (h : is_solvable (G ⧸ center G)) : is_solvable G :=
solvable_of_ker_le_range (subgroup.subtype $ center G) (quotient_group.mk' $ center G)
  (by simp only [le_refl, ker_mk, subtype_range])

variables [fintype G]

lemma card_lt_card_quotient_of_nontrivial (N : subgroup G) [nt: nontrivial N] [decidable_eq G]
  [d: decidable_pred (λ x, x ∈ N)] : card (G ⧸ N) < card G := by
{ rw card_eq_card_quotient_mul_card_subgroup N, exact lt_mul_right card_pos one_lt_card }

lemma top_eq_bot_of_trivial (h : fintype.card G = 1) : ⊥ = (⊤ : subgroup G) := by
{ apply eq_top_of_card_eq, rw h, exact card_bot }

instance solvable_of_trivial (h : card G = 1) : is_solvable G :=
is_solvable_of_top_eq_bot _ (eq.symm $ top_eq_bot_of_trivial h)

theorem p_group_solvable [decidable_eq G] (p : ℕ) [fact (nat.prime p)] (hp : is_p_group p G) :
  is_solvable G :=
begin
  have ind : ∀ n (K : Type u) [gK : group K] [fK : fintype K] [decidable_eq K]
    (hp : @is_p_group p K gK) (hK : @card K fK ≤ n), @is_solvable K gK := λ n,
  begin
    induction n with n ind; introsI K _ _ _ hp hK',
    exact false.rec _ (card_ne_zero (nat.eq_zero_of_le_zero hK')),
    by_cases hK : (card K = n.succ), unfreezingI
    { cases n,
      exact solvable_of_trivial hK,
      haveI : nontrivial K,
      { rw [←one_lt_card_iff_nontrivial, hK], exact nat.one_lt_succ_succ _ },
      haveI := is_p_group.center_nontrivial hp,
      have hq : card (K ⧸ center K) ≤ n.succ,
      { rw [←nat.succ_le_succ_iff, nat.succ_le_iff, ←hK],
        exact card_lt_card_quotient_of_nontrivial (center K) },
      have H_solvable := ind (K ⧸ center K) (is_p_group.to_quotient hp _) hq,
      exact solvable_of_solvable_quotient_center H_solvable },
    exact ind K hp (nat.le_of_lt_succ (lt_of_le_of_ne hK' hK)),
  end,
  exact ind (fintype.card G) G hp (le_refl _),
end
