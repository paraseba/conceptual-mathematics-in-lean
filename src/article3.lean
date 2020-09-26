import category_theory.category
import category_theory.isomorphism
import category_theory.types
import category_theory.isomorphism
import data.finset.basic
import data.finset.sort
import data.int.parity
import .article2


namespace exercises

universe u

section endomaps

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
lemma endo_inj (f : endomaps_map A  B) (pre) :
    (endomaps_map.mk f.map pre) = f :=
begin
    cases f,
    refl,
end

instance endo_category : category (endomap α) :=
{
    hom := λ x y, endomaps_map x y,
    id := λ x, { map := 𝟙 x.carrier, preserve := by simp }, 
    comp := λ _ _ _ f g, endomap_maps_comp f g,
    id_comp' := λ _ _ f, by {simp at *, unfold endomap_maps_comp, simp},
    comp_id' := λ _ _ f, by {simp at *, unfold endomap_maps_comp, simp},
    assoc'   := λ _ _ _ _ f g h, by {simp, unfold endomap_maps_comp, simp}
}

def Endoset := @endomap Type* category_theory.types
def Endoset_map (dom: Endoset) (ima: Endoset):= endomaps_map dom ima

def category_of_endosets := category Endoset

def x : Endoset := ⟨ ℕ, λ n, n + 2 ⟩
def y : Endoset := ⟨ ℕ, λ n, n + 1 ⟩

def yx : endomaps_map y x := {
     map := λ n:ℕ,  nat.mul n 2,
     preserve := by {
         ext a,
         change nat.mul (a + 1) 2 = (a * 2) + 2,
         simp,
         ring,
     }
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

end endomaps

section irr_graphs

variables {α β δ γ ε ζ : Type u}

structure irr_graph (α : Type u) (β : Type u) :=
(s t : α → β)

structure irr_graph_map (dom : irr_graph α β) (ima : irr_graph δ γ) :=
(fa  : α → δ)
(fd : β → γ)
(pres: fd ∘ dom.s = ima.s ∘ fa)
(pret: fd ∘ dom.t = ima.t ∘ fa)

variables {A : irr_graph α β} {B : irr_graph δ γ} {C : irr_graph ε ζ}


-- Exercise 11 page 142
def irr_graph_map_comp (f : irr_graph_map A B) (g : irr_graph_map B C) : irr_graph_map A C :=
{
    fa := g.fa ∘ f.fa,
    fd := g.fd ∘ f.fd,
    pres :=
        calc (g.fd ∘ f.fd) ∘ A.s = g.fd ∘ (f.fd ∘ A.s) : by simp
             ... = g.fd ∘ (B.s ∘ f.fa) : by rw f.pres
             ... = (g.fd ∘ B.s) ∘ f.fa : by simp
             ... = (C.s ∘ g.fa) ∘ f.fa : by rw g.pres,

    pret := by {
        calc (g.fd ∘ f.fd) ∘ A.t = g.fd ∘ (f.fd ∘ A.t) : by simp
             ... = g.fd ∘ (B.t ∘ f.fa) : by rw f.pret
             ... = (g.fd ∘ B.t) ∘ f.fa : by simp
             ... = (C.t ∘ g.fa) ∘ f.fa : by rw g.pret,
    },
}

def endo_to_irr_graph_on_obj (e: Endoset) : irr_graph e.carrier e.carrier := 
{
    s := id,
    t := e.endo
}

def endo_to_irr_graph_on_maps {A B : Endoset} (f: Endoset_map A B) :
    irr_graph_map (endo_to_irr_graph_on_obj A) (endo_to_irr_graph_on_obj B) :=
{
    fa := f.map,
    fd := f.map,
    pres := by {
        unfold endo_to_irr_graph_on_obj,
        simp,
    },
    pret := by {
        exact f.preserve,
    }
}

-- Exercise 12 page 143
lemma endo_insertion_functorial {A B C : Endoset} (f: Endoset_map A B) (g: Endoset_map B C) :
    endo_to_irr_graph_on_maps( endomap_maps_comp f g ) = irr_graph_map_comp (endo_to_irr_graph_on_maps f) (endo_to_irr_graph_on_maps g) :=
begin
    refl
end

-- Exercise 13 page 144
example {A B : Endoset} (f : irr_graph_map (endo_to_irr_graph_on_obj A) (endo_to_irr_graph_on_obj B) ) :
    ∃ g : Endoset_map A B, endo_to_irr_graph_on_maps g = f :=
begin
    have : f.fd = f.fa := f.pres,

    use f.fa,
    {
        have pret := f.pret,
        rw this at pret,
        exact pret,
    },
    {
        cases f,
        unfold endo_to_irr_graph_on_maps,
        simp,
        exact this.symm,
    }
end

end irr_graphs


section simpler

open category_theory

variables {α β: Type*}
variables [category α]

structure simpler (α : Type*) [category α] :=
(dom : α)
(ima : α)
(map : dom ⟶ ima)

structure simpler_map (dom: simpler α) (ima: simpler α) :=
(dommap : dom.dom ⟶ ima.dom)
(imamap : dom.ima ⟶ ima.ima)
(preserve : dom.map ≫ imamap = dommap ≫ ima.map)

variables {A B : simpler α}


@[simp]
lemma simpler_inj (f : simpler_map A  B) (pre) :
    (simpler_map.mk f.dommap f.imamap pre) = f :=
begin
    cases f,
    refl,
end

def simpler_maps_comp {A B C: simpler α} (f : simpler_map A B) (g : simpler_map B C) :
simpler_map A C :=
{
    dommap := f.dommap ≫ g.dommap,
    imamap := f.imamap ≫ g.imamap,
    preserve :=
       calc A.map ≫ f.imamap ≫ g.imamap
            = (f.dommap ≫ B.map) ≫ g.imamap : by rw [← category.assoc, f.preserve]
        ... = f.dommap ≫ B.map ≫ g.imamap : by  rw [category.assoc]
        ... = f.dommap ≫ g.dommap ≫ C.map : by rw [← g.preserve]
        ... = (f.dommap ≫ g.dommap) ≫ C.map : by rw [← category.assoc],
}

instance simpler_category : category (simpler α) :=
{
    hom := λ x y, simpler_map x y,
    id := λ x, { dommap := 𝟙 x.dom, imamap := 𝟙 x.ima,  preserve := by simp },
    comp := λ _ _ _ f g, simpler_maps_comp f g,
    id_comp' := λ _ _ f, by {simp at *, unfold simpler_maps_comp, simp},
    comp_id' := λ _ _ f, by {simp at *, unfold simpler_maps_comp, simp},
    assoc'   := λ _ _ _ _ f g h, by {simp, unfold simpler_maps_comp, simp}
}

def simpler_set := @simpler Type* category_theory.types
def simpler_set_map (dom: simpler_set) (ima: simpler_set):= simpler_map dom ima

def SimplerSetCategory := category simpler_set

def endo_inclusion_on_objs (e : endomap α) : simpler α := ⟨ e.carrier, e.carrier, e.endo ⟩
def endo_inclusion_on_maps {A B : endomap α } (f : endomaps_map A B) :
    simpler_map (endo_inclusion_on_objs A) (endo_inclusion_on_objs B) :=
{
    dommap := f.map,
    imamap := f.map,
    preserve := f.preserve
}

-- Exercise 14 page 144

def AddOne : simpler_set := ⟨ ℕ, ℕ, λ n, n + 1 ⟩
def AddTwo : simpler_set := ⟨ ℕ, ℕ, λ n, n + 2 ⟩

def AddOneEndo : Endoset := ⟨ ℕ, λ n, n + 1 ⟩
def AddTwoEndo : Endoset := ⟨ ℕ, λ n, n + 2 ⟩


def AddOneToAddTwo : simpler_map (endo_inclusion_on_objs AddOneEndo) (endo_inclusion_on_objs AddTwoEndo) := {
     dommap := λ n:ℕ, nat.add n  1,
     imamap := λ n:ℕ, nat.add n  2,
     preserve := by {
         ext a,
         change nat.add (a + 1) 2 = (a + 2) + 1,
         simp,
     }
}

example : ¬ ∃ f, endo_inclusion_on_maps f = AddOneToAddTwo :=
begin
    intros h,
    rcases h with ⟨ f, h⟩ ,
    unfold endo_inclusion_on_maps at h,
    unfold AddOneToAddTwo at h,
    simp at *,
    cases h,
    rw h_left at h_right,
    have := congr_fun h_right 0,
    exact (nat.succ_ne_self 1) this.symm,
end


end simpler

section ref_graphs

variables {α β δ γ ε ζ : Type u}

structure ref_graph (α : Type u) (β : Type u) extends irr_graph α β  :=
(i : β → α)
(rets: s ∘ i = id)
(rett: t ∘ i = id)


structure ref_graph_map (dom : ref_graph α β) (ima : ref_graph δ γ)
    extends irr_graph_map dom.to_irr_graph ima.to_irr_graph :=
(prei: fa ∘ dom.i = ima.i ∘ fd)

variables {A : ref_graph α β} {B : ref_graph δ γ} {C : ref_graph ε ζ}


def ref_graph_map_comp (f : ref_graph_map A B) (g : ref_graph_map B C) : ref_graph_map A C :=
{
    prei := by {
        simp,
            calc (g.fa ∘ f.fa) ∘ A.i = g.fa ∘ (f.fa ∘ A.i) : by simp
                ... = g.fa ∘ B.i ∘ f.fd : by rw f.prei
                ... = (g.fa ∘ B.i) ∘ f.fd : by simp 
                ... = (C.i ∘ g.fd) ∘ f.fd : by rw g.prei 
                ... = C.i ∘ (g.fd ∘ f.fd) : by simp,

        },

    ..irr_graph_map_comp f.to_irr_graph_map g.to_irr_graph_map,
}

-- Exercise 15 page 145
example : (A.i ∘ A.s) ∘ (A.i ∘ A.s) = A.i ∘ A.s :=
calc (A.i ∘ A.s) ∘ (A.i ∘ A.s) = A.i ∘ (A.s ∘ A.i) ∘ A.s : by simp
    ... = A.i ∘ A.s : by simp[A.rets]

example : (A.i ∘ A.t) ∘ (A.i ∘ A.t) = A.i ∘ A.t :=
calc (A.i ∘ A.t) ∘ (A.i ∘ A.t) = A.i ∘ (A.t ∘ A.i) ∘ A.t : by simp
    ... = A.i ∘ A.t : by simp[A.rett]

example : (A.i ∘ A.t) ∘ (A.i ∘ A.s) = A.i ∘ A.s :=
calc (A.i ∘ A.t) ∘ (A.i ∘ A.s) = A.i ∘ (A.t ∘ A.i) ∘ A.s : by simp
    ... = A.i ∘ A.s : by simp[A.rett] 

example : (A.i ∘ A.s) ∘ (A.i ∘ A.t) = A.i ∘ A.t :=
calc (A.i ∘ A.s) ∘ (A.i ∘ A.t) = A.i ∘ (A.s ∘ A.i) ∘ A.t : by simp
    ... = A.i ∘ A.t : by simp [A.rets]

-- Exercise 16 page 145
example (f : ref_graph_map A B) : f.fd = B.s ∘ f.fa ∘ A.i :=
calc f.fd = (B.s ∘ B.i) ∘ f.fd : by simp [B.rets]
     ... = B.s ∘ (B.i ∘ f.fd) : by simp
     ... = B.s ∘ f.fa ∘ A.i : by rw f.prei

end ref_graphs

end exercises