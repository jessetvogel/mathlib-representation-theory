import ring_theory.ideal.basic
import algebra.module.submodule.basic
import ring_theory.simple_module
import group_theory.free_abelian_group_finsupp
import order.jordan_holder
import ring_theory.artinian
import algebra.direct_sum.basic

open_locale direct_sum
open ideal

classical

-- Some properties of morphisms
section morphisms

variables {R M N : Type*} [ring R] [add_comm_group M] [module R M] [add_comm_group N]
  [module R N] (f : M →ₗ[R] N)

abbreviation im : submodule R N := submodule.map f ⊤
abbreviation ker : submodule R M := submodule.comap f ⊥
abbreviation coker := N ⧸ im f

end morphisms

-- Some properties of simple modules
section simple

instance nontrivial_of_simple {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (h : is_simple_module R M) : nontrivial M :=
begin
  rcases h.to_nontrivial with ⟨a, b, hab⟩,
  have hab' : a.carrier ≠ b.carrier, {
    intro h,
    apply hab,
    cases a,
    cases b,
    simp only,
    exact h,
  },
  have h' : ¬ ( a.carrier ⊆ b.carrier ∧ b.carrier ⊆ a.carrier ), {
    intro h,
    apply hab',
    sorry,
  },
  have h'' : (¬ a.carrier ⊆ b.carrier) ∨ (¬ b.carrier ⊆ a.carrier), {
    sorry,
  },
  wlog h''' : (¬ a.carrier ⊆ b.carrier) using a b,
  exact h'',
  sorry,
end

lemma nonzero_of_nontrivial {M : Type*} [add_comm_group M] (t : nontrivial M) : ∃ x : M, x ≠ 0 :=
begin
  have t' := t,
  rcases t' with ⟨a, b, hab⟩,
  use a-b,
  intro h,
  apply hab,
  sorry,
end

end simple

-- Jordan Holder
section JordanHolder

open submodule

instance jordan_holder_module {R M : Type*} [ring R] [add_comm_group M] [module R M] :
  jordan_holder_lattice (submodule R M) := {
  is_maximal := λ A B, (A ≤ B) ∧
    (∀ h : A ≤ B, is_simple_module R (coker $ of_le h)),
  lt_of_is_maximal := λ A B h, begin
    apply lt_of_le_of_ne h.1,
    intro hAB,
    cases nonzero_of_nontrivial (nontrivial_of_simple $ h.2 h.1) with x hx,
    apply hx,
    -- let z := quotient.exists_rep x,
    sorry,
  end,
  sup_eq_of_is_maximal := sorry,
  is_maximal_inf_left_of_is_maximal_sup := sorry,
  iso := λ X Y, ∀ hX : X.1 ≤ X.2, ∀ hY : Y.1 ≤ Y.2,
    nonempty $ (coker (of_le hX)) ≃ₗ[R] coker (of_le hY),
  iso_symm := begin
    sorry,
  end,
  iso_trans := sorry,
  second_iso := sorry
}

end JordanHolder

-- Composition serier
section composition_series

lemma finite_composition_series_of_artinian {R : Type*} [ring R] (M : Type*) [add_comm_group M]
  [module R M] [is_artinian R M] (N : submodule R M) :
  (λ s : composition_series (submodule R M), s.top).surjective :=
begin
  sorry,
end

end composition_series

-- Grothendieck ring
section grothendieck

structure max_spec (R : Type*) [ring R] := (ideal : ideal R) (is_maximal : is_maximal ideal)
def grothendieck_ring (R : Type*) [ring R] := (max_spec R) →₀ ℤ

namespace grothendieck
variables (R : Type*) [ring R] (M : Type*) [add_comm_group M] [module R M] [is_artinian R M]

def mk'' (S : composition_series (submodule R M)) : grothendieck_ring R :=
begin
  -- take quotients
  -- convert to maximal ideals
  -- map to grothendieck_ring
  sorry
end

def mk' (N : submodule R M) : grothendieck_ring R :=
begin
  -- pick a composition series for N
  -- prove that well defined up to equivalence
  sorry
end

def mk : grothendieck_ring R := mk' R M ⊤

end grothendieck
end grothendieck
