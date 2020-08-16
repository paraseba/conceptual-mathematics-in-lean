import category_theory.category

namespace magma

structure magma :=
(carrier : Type)
(mul : carrier -> carrier -> carrier)

instance {m: magma}: has_mul m.carrier :=  ⟨ m.mul ⟩


structure magma_hom (m1: magma) (m2: magma) :=
(to_fun : m1.carrier → m2.carrier)
(preserves : ∀ x y : m1.carrier, to_fun (x * y) = to_fun x * to_fun y)

infixr ` m→ `:25 := magma_hom


variables {m n o: magma}

instance : has_coe_to_fun (m m→ n) := ⟨_, magma_hom.to_fun⟩

lemma to_fun_eq_coe (f : m m→ n) : f.to_fun = f := rfl

@[simp]
lemma coe_mk (f : m.carrier → n.carrier) (pre) : ⇑(magma_hom.mk f pre) = f := rfl

lemma coe_inj ⦃f g : m m→ n⦄ (h : (f : m.carrier → n.carrier) = g) : f = g :=
begin
    cases f; cases g; cases h; refl,
end

@[ext]
lemma magma_hom_ext ⦃f g : m m→ n⦄ (h : ∀ x, f x = g x) : f = g :=
coe_inj (funext h)


def magma_id : m m→ m := ⟨id, by simp⟩

def magma_hom_comp (f: m m→ n) (g: n m→ o) : m m→ o :=
{
  to_fun := g.to_fun ∘ f.to_fun,
  preserves := by {
      intros x y,
      simp,
      rw f.preserves,
      rw g.preserves
  }
} 

open category_theory

instance : has_hom magma := ⟨ λ m n, m m→ n ⟩

instance : category_struct magma := ⟨ @magma_id, @magma_hom_comp ⟩

instance : category magma := {}

end magma
