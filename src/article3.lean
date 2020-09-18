import category_theory.category
import category_theory.isomorphism
import category_theory.types
import category_theory.isomorphism
import .article2


namespace exercises

universe u

open category_theory

variables {α β: Type*}
variables [category α]

structure endomap (α : Type*) [category α] :=
(carrier : α)
(endo : carrier ⟶ carrier)

structure endomaps_map (dom: endomap α) (ima: endomap α) :=
(map : dom.carrier ⟶ ima.carrier)
(preserve : dom.endo ≫ map = map ≫ ima.endo)

-- Exercise 1 page 137
def endomap_maps_comp {A B C: endomap α} (f : endomaps_map A B) (g : endomaps_map B C) : endomaps_map A C :=
{
    map := f.map ≫ g.map,
    preserve :=
       calc A.endo ≫ f.map ≫ g.map = (f.map ≫ B.endo) ≫ g.map : by rw [← category.assoc, f.preserve]
            ... = f.map ≫ g.map ≫ C.endo : by simp [g.preserve]
            ... = (f.map ≫ g.map) ≫ C.endo : by simp,
}

variables {A B : endomap α}

@[simp]
lemma coe_mk (f : endomaps_map A  B) (pre) : (endomaps_map.mk f.map pre) = f := by {sorry}

lemma coe_inj ⦃f g : endomaps_map A B⦄ (h : (f : endomaps_map A B) = g) : f = g :=
begin
    cases f, cases g,
    exact h,
end

--@[ext]
--lemma endo_hom_ext ⦃f g : endomaps_map A B⦄ (h : ∀ x, f x = g x) : f = g :=
    --coe_inj _ _ (funext h)

instance endo_category : category (endomap α) :=
{
    hom := λ f g, endomaps_map f g,
    id := λ x, ⟨ 𝟙 x.carrier, by simp ⟩, 
    comp := λ _ _ _ f g, endomap_maps_comp f g,
    id_comp' := λ _ _ f, by {simp at *,unfold endomap_maps_comp,simp},
    comp_id' := λ _ _ f, by {simp at *,unfold endomap_maps_comp,simp},
    assoc'   := λ _ _ _ _ f g h, by {simp, unfold endomap_maps_comp, simp}
}

-- Exercise 2 page 139
example {X: α} (endo r : X ⟶ X) (idem : idempotent endo) (ret : is_retraction endo r) : endo = 𝟙 X :=
    calc endo = endo ≫ 𝟙 X : by simp
        ... = endo ≫ (endo ≫ r) : by {unfold is_retraction at ret, rw ←ret}
        ... = (endo ≫ endo) ≫ r : by simp
        ... = endo ≫ r : by rw idempotent.repeat
        ... = 𝟙 X : ret

def involution {A : α} (f : A ⟶ A) := f ≫ f = 𝟙 A 

-- Exercise 4 page 140
def minus : endomap Type*  := {
    carrier := ℤ, 
    endo := λ x, -x
}

example  : @involution Type*  infer_instance ℤ (λ x:ℤ, -x) :=
begin
    unfold involution,
    ext,
    simp,
end

-- Exercise 5 page 140
example  : @idempotent Type*  infer_instance ℤ (λ x:ℤ, abs x) := {
    repeat := by {
        simp,
        ext,
        rw ← abs_abs,
        simp,
    }
}

-- Exercise 6 page 140
example  : @is_iso Type* infer_instance ℤ ℤ  (λ x:ℤ, x + 3) := {
    inv := λ x, x - 3,
}

lemma prod_ne_one_of_gr {a b: ℤ} (h: b > 1) : a * b ≠ 1 :=
begin
    intros prod,
    have h := int.eq_one_of_mul_eq_one_left (by linarith) prod,
    linarith,
end

-- Exercise 7 page 140
example (iso: @is_iso Type* infer_instance ℤ ℤ  (λ x:ℤ, x * 5)) : false :=
begin
    have : iso.inv ≫ (λ x:ℤ, x * 5) = 𝟙 ℤ := @is_iso.inv_hom_id Type* infer_instance ℤ ℤ  (λ x:ℤ, x * 5) iso,
    have h := congr_fun this 1,
    simp at h,
    exact prod_ne_one_of_gr (by linarith) h ,
end

-- Exercise 8 page 140
example (A : α)  (f : A ⟶ A) (inv: involution f) : f ≫ f ≫ f = f :=
begin
    unfold involution at inv,
    rw inv,
    exact category.comp_id _,
end

example (A : α)  (f : A ⟶ A) [ide: idempotent f] : f ≫ f ≫ f = f :=
begin
    rw ide.repeat,
    rw ide.repeat,
end


end exercises