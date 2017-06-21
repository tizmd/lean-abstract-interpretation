import algebra.lattice.dcpo 
universe u
open lattice 

namespace lattice 

inductive flat (α : Type u) : Type u 
| bot {} : flat 
| top {} : flat 
| elem   : Π a : α, flat 

instance {α : Type u} : has_bot (flat α) := ⟨ flat.bot ⟩ 
instance {α : Type u} : has_top (flat α) := ⟨ flat.top ⟩ 

namespace flat 
variables {α : Type u}[decidable_eq α]

protected 
def sup : flat α → flat α → flat α
| bot y := y
| x  bot := x
| top _ := top 
| _ top := top 
| (elem a) (elem b) := if a = b then elem a else top 

instance : has_sup (flat α) := ⟨ flat.sup ⟩ 

@[simp]
lemma sup_bot_left  (x : flat α) : ⊥ ⊔ x = x := match x with 
                                                | bot := rfl
                                                | top := rfl 
                                                | (elem _) := rfl
                                                end

@[simp]
lemma sup_bot_right : Π (x : flat α), x ⊔ ⊥ = x
| bot := rfl 
| top := rfl 
| (elem _) := rfl 

@[simp]
lemma sup_top_left : Π (x : flat α), ⊤ ⊔ x = ⊤ 
| bot := rfl 
| top := rfl 
| (elem _) := rfl 

@[simp]
lemma sup_top_right : Π (x : flat α), x ⊔ ⊤ = ⊤ 
| bot := rfl 
| top := rfl 
| (elem _) := rfl 

@[simp]
lemma sup_idem : Π (x : flat α), x ⊔ x = x 
| bot := rfl 
| top := rfl 
| (elem _) := if_pos rfl

lemma sup_comm : Π {x y : flat α}, x ⊔ y = y ⊔ x 
| bot _ := rfl 
| top _ := rfl 
| _   bot := rfl 
| _  top := rfl 
| (elem a) (elem b) := if H : a = b then 
                          eq.rec_on H (eq.trans sup_idem sup_idem.symm) 
                          else 
                          begin 
                          unfold has_sup.sup, 
                          simp [flat.sup],
                          rw if_neg H,
                          rw if_neg (ne.symm H),
                          end

protected 
def inf : flat α → flat α → flat α
| bot _ := bot
| _ bot := bot
| top y := y 
| x top := x 
| (elem a) (elem b) := if a = b then elem a else bot

instance : has_inf (flat α) := ⟨ flat.inf ⟩ 

protected 
def le (x y : flat α) : Prop := y = x ⊔ y
instance : has_le (flat α) := ⟨flat.le⟩ 

protected 
lemma bot_le {x : flat α} : ⊥ ≤ x := match x with 
                                   | bot     := rfl 
                                   | top     := rfl 
                                   | elem _  := rfl
                                   end
lemma eq_of_le_bot {x : flat α} : x ≤ ⊥ → x = ⊥ := 
  begin intro h, cases x, refl, contradiction, contradiction end
  
protected 
lemma  le_top {x : flat α} : x ≤ ⊤  := match x with 
                                   | bot     := rfl 
                                   | top     := rfl 
                                   | elem _  := rfl
                                   end
lemma eq_of_top_le {x : flat α} : ⊤ ≤ x → x = ⊤ := 
  begin intro h, cases x, contradiction, refl, contradiction end

@[refl]
protected lemma le_refl : ∀ x : flat α, x ≤ x := take x, sup_idem.symm  

@[trans]
protected lemma le_trans : ∀ x y z : flat α, x ≤ y → y ≤ z → x ≤ z 
| bot _ _ := assume hxy hyz, flat.bot_le
| top _ _ := assume hxy, eq.rec_on (eq_of_top_le hxy).symm 
            (assume hyz, eq.rec_on (eq_of_top_le hyz).symm (flat.le_refl _))
| _ bot _ := assume hxy hyz, eq.rec_on (eq_of_le_bot hxy).symm flat.bot_le
| _ top _ := assume hxy hyz, eq.rec_on (eq_of_top_le hyz).symm flat.le_top
| _ _   bot := begin intros hxy hyz, revert hxy, rw eq_of_le_bot hyz, intro hxy, rw eq_of_le_bot hxy, refl end 
| _ _  top  := assume hxy hyz, flat.le_top
| (elem a) (elem b) (elem c) := assume hxy hyz, 
                                if Hab : a = b then eq.rec_on Hab.symm hyz 
                                else begin 
                                        assert H : elem b = flat.sup (elem a) (elem b),
                                          assumption,
                                        assert eq : elem b = ⊤, 
                                          rw H,
                                          simp [flat.sup],
                                          rw if_neg Hab, refl,
                                        contradiction
                                     end
protected lemma le_antisymm (x y : flat α) : x ≤ y → y ≤ x → x = y 
:= assume hxy hyx, eq.trans hyx (eq.trans sup_comm hxy.symm)

protected lemma le_sup_left (x y : flat α) : x ≤ x ⊔ y :=  
end flat 
end lattice
