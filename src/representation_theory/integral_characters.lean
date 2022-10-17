import representation_theory.character
import ring_theory.integral_closure
import ring_theory.roots_of_unity
import field_theory.is_alg_closed.algebraic_closure

universe u
variables {k G : Type u} [field k] [group G]

namespace fdRep

-- Theorem 11.9.
theorem integral_character (V : fdRep k G) (g : G) : is_integral k (character V g) :=
begin
  sorry,
end

-- Lemma 11.10
lemma roots_of_unity_properties (n : ℕ+) (l : list (roots_of_unity n k)) :
let s : k := (list.sum (list.map coe l)) in let t : k := l.length in
tfae [
  t ∣ s,
  ∀ a b : roots_of_unity n k, a ∈ l → b ∈ l → a = b
-- ... (Should we use complex numbers?)
] :=
begin
  dsimp,
  tfae_have : 1 → 2, {
    intros h a b ha hb,
    sorry,
  },
  tfae_have : 2 → 1, {
    intro h,
    sorry,
  },
  tfae_finish,
end

end fdRep
