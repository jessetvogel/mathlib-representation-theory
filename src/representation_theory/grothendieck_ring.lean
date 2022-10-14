import ring_theory.ideal.basic
import algebra.module.submodule.basic
import ring_theory.simple_module
import group_theory.free_abelian_group_finsupp
import order.jordan_holder
import ring_theory.artinian
import algebra.direct_sum.basic

open_locale direct_sum
open ideal

theorem maximal_quot_is_simple {R : Type*} [ring R] {I : ideal R} (h : is_maximal I) :
  is_simple_module R (R ⧸ I) := is_simple_module_iff_is_coatom.mpr h.out

structure max_spec (R : Type*) [ring R] := (ideal : ideal R) (is_maximal : is_maximal ideal)

def submodule_inclusion {R M : Type*} [ring R] [add_comm_monoid M] [module R M] (A : submodule R M) :
  A →+ M := add_submonoid_class.subtype A

def image_restriction {R M N : Type*} [ring R] [add_comm_monoid M] [add_comm_monoid N] [module R M]
  [module R N] (I : submodule R N) (f : M →+ N) (h : set.image f ⊤ ≤ I ) : M →+ I :=
begin
  refine add_monoid_hom.cod_restrict f I _,
  intro x,
  sorry,
end

def subsubmodule_inclusion {R M :Type*} [ring R] [add_comm_monoid M] [module R M] (A B : submodule R M)
  (h : A ≤ B) : A →+ B :=
begin
  refine add_monoid_hom.restrict _ A,
  apply image_restriction,
  swap,
  split,
  rotate 2,
  exact id,
  suggest,
end

def submodule_coe {R M : Type*} [ring R] [add_comm_monoid M] [module R M]
  (A B : submodule R M) (h : A ≤ B) : submodule R B := {
  carrier := set.preimage (@coe B M _) A,
  add_mem' := λ a b, submodule.add_mem A,
  zero_mem' := _,
  smul_mem' := _ }

instance jordan_holder_module {R M : Type*} [ring R] [add_comm_monoid M] [module R M] :
  jordan_holder_lattice (submodule R M) := {
  is_maximal := λ A B, (A ≤ B) ∧ (A ≤ B → A ⧸ B),
  lt_of_is_maximal := _,
  sup_eq_of_is_maximal := _,
  is_maximal_inf_left_of_is_maximal_sup := _,
  iso := _,
  iso_symm := _,
  iso_trans := _,
  second_iso := _
}

lemma finite_composition_series_of_artinian {R : Type*} [ring R] (M : Type*) [add_comm_monoid M]
  [module R M] [is_artinian R M] (N : submodule R M) :
  (λ s : composition_series (submodule R M), s.top).surjective :=
begin
  sorry,
end


def grothendieck_ring (R : Type*) [ring R] := (max_spec R) →₀ ℤ

section
variables (R : Type*) [ring R] (M : Type*) [add_comm_monoid M] [module R M] [is_artinian R M]

def grothendieck_ring_mk'' (S : composition_series (submodule R M)) : grothendieck_ring R :=
begin
  -- take quotients
  -- convert to maximal ideals
  -- map to grothendieck_ring
  sorry
end

def grothendieck_ring_mk' (N : submodule R M) :
  grothendieck_ring R :=
begin
  -- pick a composition series for N
  -- prove that well defined up to equivalence
  sorry
end

def grothendieck_ring_mk : grothendieck_ring R := grothendieck_ring_mk' R M ⊤

end
