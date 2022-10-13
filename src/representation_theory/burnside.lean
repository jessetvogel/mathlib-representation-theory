import group_theory.solvable number_theory.basic

section
open nat.prime

def is_burnside (G : Type*) : Prop := ∃ p q a b: ℕ, p.prime ∧ q.prime ∧ nat.card G = p^a * q^b

lemma finite_of_is_burnside {G : Type*} (h : is_burnside G) : finite G :=
begin
  have h : nat.card G ≠ 0 := begin
    rcases h with ⟨p, q, a, b, hp, hq, hc⟩,
    have hp' := pow_ne_zero a hp.ne_zero,
    have hq' := pow_ne_zero b hq.ne_zero,
    rw hc,
    exact mul_ne_zero hp' hq',
  end,
  exact nat.finite_of_card_ne_zero h,
end

variables {G : Type*} [group G] (p q : ℕ) [fact p.prime] [fact q.prime]

theorem solvable_of_burnside (h : is_burnside G) : is_solvable G :=
begin
  sorry,
end
