import algebra.lattice.basic algebra.lattice.bounded_lattice algebra.lattice.complete_lattice
import data.set 

universes u v w
open lattice
set_option old_structure_cmd true 
set_option eqn_compiler.zeta true

variables {α : Type u} {β : Type v}{γ : Type w}

private lemma exists_add_of_le : ∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k := 
  begin
   intros m n hle,
   existsi n - m,
   rw [nat.add_sub_of_le],
   assumption
  end

def is_directed [weak_order α] (s : set α) := ∀ a b ∈ s, ∃ c, c ∈ s ∧ a ≤ c ∧ b ≤ c 
def is_chain [weak_order α] (s : set α)  := ∀ a b ∈ s, a ≤ b ∨ b ≤ a 

def chain [weak_order α] := {s : set α // is_chain s}

def ascending_chain α [weak_order α] := { f : ℕ → α //  ∀ n, f n ≤ f (n + 1) }

namespace ascending_chain
variables [weak_order α] 

protected
def mem (a : α)(f : ascending_chain α) : Prop := ∃ n : ℕ, a = f.1 n
instance : has_mem α (ascending_chain α) := ⟨ ascending_chain.mem ⟩  

def monotone (f : ascending_chain α) {m n} : m ≤ n → f.1 m ≤ f.1 n :=     
begin 
intro hle,
cases (exists_add_of_le hle) with k hk,
rw hk,
clear hk,
induction k with k iH,
refl,
transitivity f.1 (m + k),
assumption,
rw nat.add_succ,
apply f.property
end

def is_stationary (f : ascending_chain α) : Prop := ∃ n, ∀ m, n ≤ m → f.1 n = f.1 m 

end ascending_chain

def iter_n (f : α → α) (z : α) : ℕ → α 
|  0 := z 
|  (n + 1) := f $ iter_n n


namespace iter_n 
variables [weak_order α] {f : α → α}

lemma single_step {z : α} : monotone f → z ≤ f z → ∀ {{n : ℕ}}, iter_n f z n ≤ iter_n f z (n+1) := 
  begin
    intros hmono hini n,
    induction n with n iH,
     assumption,
     apply hmono, assumption
  end     

def to_ascending_chain {f} {z} : monotone f → z ≤ f z → ascending_chain α := 
  assume hmono hini, ⟨iter_n f z, take n, begin apply single_step, repeat {assumption} end⟩ 

lemma upper_bound (a : α) {z} : monotone f → z ≤ a → f a ≤ a → ∀ {{n}}, iter_n f z n ≤ a := 
assume hmono hini hle, 
  take n,
    nat.rec_on n hini (take n, assume iH, calc iter_n f z (n+1) = f (iter_n f z n) : by refl 
                                                            ... ≤ f a              : hmono iH 
                                                            ... ≤ a                : hle  
                      )

end iter_n

def iter_n₁ (f : α → α) : ℕ → α → α 
| 0 := id 
| (n+1) := λ a, iter_n₁ n $ f a

namespace iter_n₁ 
variables {f : α → α}

@[simp]
lemma iter_eq : ∀ {n}{z}, iter_n₁ f (n+1) z = f (iter_n₁ f n z) 
| 0 _ := rfl 
| (n+1) z := calc iter_n₁ f (n + 2) z = iter_n₁ f (n + 1) (f z) : by refl 
                                 ...  = f (iter_n₁ f n (f z))   : by rw iter_eq 
                                 ...  = f (iter_n₁ f (n+1) z)   : by refl 

lemma single_step [weak_order α] {z} (hmono : monotone f) (hini : z ≤ f z) : ∀ n, iter_n₁ f n z ≤ iter_n₁ f (n+1) z 
| 0     := hini 
| (n+1) := calc iter_n₁ f (n+1) z = f (iter_n₁ f n z)     : iter_eq 
                            ...   ≤ f (iter_n₁ f (n+1) z) : hmono (single_step n) 
                            ...   = iter_n₁ f (n+2) z     : iter_eq.symm 

def to_ascending_chain [weak_order α] {z} : monotone f → z ≤ f z → ascending_chain α := 
  assume hmono hini, ⟨_, single_step hmono hini⟩ 
   
end iter_n₁

namespace is_directed 

lemma empty [weak_order α] : is_directed (∅ : set α) := take a b, false.elim

lemma univ  [semilattice_sup α] : is_directed (set.univ : set α) := 
    take a b, assume ha hb, ⟨a ⊔ b , true.intro ,le_sup_left  , le_sup_right⟩  

lemma singleton [weak_order α] {a} : is_directed ({a} : set α) := 
   take x y, assume hx hy, 
      have eqx : x = a, from or.resolve_right hx false.elim,
      have eqy : y = a, from or.resolve_right hy false.elim,
      by rw [eqx, eqy]; exact ⟨a, or.inl rfl, le_refl _ , le_refl _⟩ 

lemma of_is_chain [weak_order α] { s : set α } : is_chain s → is_directed s := 
   assume h, take x y, assume hx hy, 
   or.elim  (h _ _ hx hy) 
      (assume hxy, ⟨_, hy, hxy, by refl⟩) 
      (assume hyx, ⟨_, hx, by refl, hyx⟩) 

lemma of_ascending_chain [weak_order α](f : ascending_chain α) : is_directed { a : α | a ∈ f } := 
  take x y, assume ⟨m, hm⟩ ⟨n, hn⟩,  
    eq.rec_on hm.symm 
    (eq.rec_on hn.symm 
      (match le_total m n with 
       | or.inl hmn := ⟨f.1 n, ⟨_, rfl⟩, f.monotone hmn , by refl⟩  
       | or.inr hnm := ⟨f.1 m, ⟨_, rfl⟩, by refl , f.monotone hnm⟩  
       end
      )
    )
 lemma of_lower_set [weak_order α] (a : α) : is_directed ({ x | x ≤ a}) := 
   take x y, assume hx hy, ⟨a, le_refl _, hx, hy⟩   

end is_directed

def directed α [weak_order α] := { s : set α // is_directed s }

instance [weak_order α] : has_mem α (directed α) := ⟨ λ a s, a ∈ s.1⟩  
instance [weak_order α] : has_emptyc (directed α) := ⟨ ⟨_, is_directed.empty⟩ ⟩  
instance [weak_order α] : has_subset (directed α) := ⟨ λ s t, s.1 ⊆ t.1 ⟩ 

def directed.of_ascending_chain [weak_order α] : ascending_chain α → directed α := λ seq, ⟨_, is_directed.of_ascending_chain seq⟩  
def directed.of_lower_set [weak_order α] : α → directed α := λ a, ⟨_, is_directed.of_lower_set a⟩  

class directed_complete_partial_order α extends weak_order α := 
  (dSup : directed α → α)
  (le_dSup : ∀ s, ∀ a ∈ s, a ≤ dSup s)  
  (dSup_le : ∀ s a, (∀ b∈s, b ≤ a) → dSup s ≤ a)

def dSup [directed_complete_partial_order α] : directed α → α := directed_complete_partial_order.dSup 

section 
variables [directed_complete_partial_order α]{s t : directed α} {a b : α}

lemma le_dSup : a ∈ s → a ≤ dSup s := directed_complete_partial_order.le_dSup s a 
lemma dSup_le : (∀ b ∈ s, b ≤ a) → dSup s ≤ a := directed_complete_partial_order.dSup_le s a 
lemma le_dSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ dSup s := le_trans h (le_dSup hb) 

lemma dSup_le_dSup (h : s ⊆ t) : dSup s ≤ dSup t := 
  dSup_le ( take a, assume ha : a ∈ s, le_dSup $ h ha)
end 
namespace directed_complete_partial_order 

variables [directed_complete_partial_order α] {a b : α}

def bot : α := dSup ∅  
lemma bot_le : bot ≤ a := 
  dSup_le _ _ (take b, false.elim) 

  
end directed_complete_partial_order

instance directed_complete_partial_order_bot [ ins : directed_complete_partial_order α] : order_bot α := 
{
  ins with 
  bot := directed_complete_partial_order.bot,
  bot_le := @directed_complete_partial_order.bot_le _ _,
}

class directed_complete_partial_order_sup α extends semilattice_sup α , directed_complete_partial_order α 

instance directed_complete_partial_order_sup_top [ ins : directed_complete_partial_order_sup α] : semilattice_sup_top α := 
{
  ins with 
  top := dSup ⟨set.univ, take x y, assume hx hy, ⟨_ , true.intro, le_sup_left, le_sup_right⟩⟩,  
  le_top := take _, le_dSup true.intro
}

instance complete_lattice_directed_complete_partial_order_sup [ins : complete_lattice α] : directed_complete_partial_order_sup α := 
{
    ins with 
    dSup := λ s, Sup s.1,
    le_dSup := λ s a, assume ha, le_Sup ha,
    dSup_le := λ s a, assume h, Sup_le (take _ hb, h _ hb) 
} 

structure is_scott_continuous [directed_complete_partial_order α] [directed_complete_partial_order β] (f : α → β) : Prop := 
  (preserve_directed : ∀ s : directed α, is_directed (set.image f s.1))
  (preserve_dSup     : ∀ s : directed α, f (dSup s) = dSup ⟨_, preserve_directed s⟩)

namespace is_scott_continuous 
variables [directed_complete_partial_order α] [directed_complete_partial_order β][directed_complete_partial_order γ] 
   {f : α → β}{g : β → γ}

private lemma set_image_id {α : Type u} {s : set α} : set.image (@id α) s = s := 
  set.ext (take a, iff.intro (assume ⟨_, hx, eqx⟩, eq.rec_on eqx hx) 
                             (assume ha, ⟨_, ha, rfl⟩ ))
protected
lemma id : is_scott_continuous (@id α) := 
  ⟨ λ s, begin rw set_image_id, apply s.2 end , take s, begin simp, apply congr_arg, symmetry, apply subtype.eq, apply set_image_id end ⟩ 

protected
lemma comp : is_scott_continuous g → is_scott_continuous f → is_scott_continuous (g ∘ f) := 
  assume hg hf, 
    have pr_dir : ∀ s : directed α, is_directed (set.image (g ∘ f) s.1), 
       from 
          take sa, take c₁ c₂, assume ⟨a₁, ha₁, eqc₁⟩ ⟨a₂, ha₂, eqc₂⟩, 
            let sb : directed β := ⟨_, hf.preserve_directed sa⟩ in
            match (hg.preserve_directed sb _ _ ⟨_, ⟨_, ha₁, rfl⟩, eqc₁⟩ ⟨_, ⟨_, ha₂, rfl⟩, eqc₂⟩) with
            | ⟨c, ⟨b, ⟨a, ha, hab⟩ , hbc ⟩, hfc₁c, hfc₂c⟩ := 
              ⟨c, ⟨a, ha, begin rw -hab at hbc, assumption end⟩  , hfc₁c , hfc₂c ⟩  
            end,
    ⟨pr_dir, 
      take sa, 
        let sb : directed β := ⟨_, hf.preserve_directed sa⟩ in
        show g (f (dSup sa)) = dSup ⟨_, pr_dir sa⟩, 
          from begin
                 rw hf.preserve_dSup,
                 rw hg.preserve_dSup,
                 apply congr_arg, apply subtype.eq,
                 apply set.ext, 
                 intro c, 
                 apply iff.intro,
                  {
                      intro h,
                      cases h with b hb,
                      cases hb with hb eqbc,
                      cases hb with a ha,
                      cases ha with ha eqab,
                      rw -eqab at eqbc,
                      exact ⟨_, ha, eqbc⟩ 
                  },
                  {
                      intro h,
                      cases h with a ha,
                      cases ha with ha eqac,
                      exact ⟨_, ⟨_, ha, rfl⟩, eqac⟩ 
                  }
               end 
      ⟩ 
            
 
lemma monotone : is_scott_continuous f → monotone f := 
 assume hcont, take a b, assume hab,
    have ab_is_chain : is_chain ({a,b} : set α), 
       from begin 
             intros x y hx hy,
             cases hx with xb hx,
               rw xb, 
               cases hy with yb hy,
               rw yb, simp,
               cases hy with ya hy,
               simph, 
               apply false.elim, assumption,
            cases hx with xa hx,
               rw xa,
               cases hy with yb hy, 
               rw yb, left, assumption,
               cases hy with ya hy,
               simph,
               apply false.elim, assumption,
            apply false.elim, assumption
            end,
    let s : directed α := ⟨_, is_directed.of_is_chain ab_is_chain⟩ in
    have H : dSup s = b, 
      from begin 
            apply le_antisymm,
             { apply dSup_le, 
               intros x hx,
               cases hx with xb hx,
                 rw xb,
               cases hx with xa hx,
                 rw xa, assumption,
               apply false.elim, assumption
             },
             {
                 apply le_dSup,
                 apply or.inl, refl
             }
           end,
    let s_image : directed β := ⟨_, hcont.preserve_directed s⟩ in 
    have fH : dSup s_image = f b, 
      from begin 
            rw -hcont.preserve_dSup,
            rw H
           end,
    show f a ≤ f b, 
      from begin
            rw -fH,
            apply le_dSup,
            exact ⟨_, or.inr (or.inl rfl), rfl⟩ 
           end
  private lemma set_image_empty {α}{β} {f : α → β} : set.image f ∅ = ∅ := 
     set.ext (take x, ⟨ assume ⟨_, h, _⟩, h.elim, false.elim ⟩ )

  lemma is_strict : is_scott_continuous f → f ⊥ = ⊥ := 
    assume hcont, eq.trans (hcont.preserve_dSup ∅) (congr_arg dSup (subtype.eq set_image_empty))


end is_scott_continuous

def scott_continuous α β [directed_complete_partial_order α] [directed_complete_partial_order β] := { f : α → β // is_scott_continuous f }

namespace scott_continuous 

variables [directed_complete_partial_order α] [directed_complete_partial_order β][directed_complete_partial_order γ]
 {f : scott_continuous α β} {g : scott_continuous β γ}
protected
def id : scott_continuous α α := ⟨ _, is_scott_continuous.id⟩ 
protected
def comp : scott_continuous β γ → scott_continuous α β → scott_continuous α γ := take g f, ⟨_, is_scott_continuous.comp g.2 f.2⟩ 
protected
def monotone (f : scott_continuous α β) : monotone f.1 := f.2.monotone 


protected 
def le (f g : scott_continuous α β) : Prop := ∀ a , f.1 a ≤ g.1 a  

instance : has_le (scott_continuous α β) := ⟨ scott_continuous.le ⟩ 

@[refl]
protected 
def le_refl (f : scott_continuous α β) : f ≤ f := take a : α, le_refl _

@[trans]
protected 
def le_trans  (f g h : scott_continuous α β) : f ≤ g → g ≤ h → f ≤ h := take hfg hgh, take a, le_trans (hfg a) (hgh a) 

protected
def le_antisymm (f g : scott_continuous α β) : f ≤ g → g ≤ f → f = g := 
  take hfg hgf, subtype.eq (funext (take a, le_antisymm (hfg a) (hgf a))) 

instance scott_continuous_weak_order : weak_order (scott_continuous α β) := 
{
    le := scott_continuous.le,
    le_refl := scott_continuous.le_refl,
    le_trans := scott_continuous.le_trans,
    le_antisymm := scott_continuous.le_antisymm
}
/-
protected
def sup (f g : scott_continuous α β) : scott_continuous α β := 
  let h := λ a, f.1 a ⊔ g.1 a in  
  have h_monotone : monotone h, from 
    take a b, assume hab, sup_le_sup (f.monotone hab) (g.monotone hab),
  have pr_dir : ∀ s : directed α, is_directed (set.image h s.1), 
    from take s, take b₁ b₂, assume ⟨a₁, ha₁, eqa₁⟩ ⟨a₂, ha₂, eqa₂⟩,      
         match s.property _ _ ha₁ ha₂ with 
         | ⟨b, bmem, ha₁b, ha₂b⟩ := 
           ⟨_, ⟨_, bmem, rfl⟩, eq.rec_on eqa₁ (h_monotone ha₁b), eq.rec_on eqa₂ (h_monotone ha₂b)⟩  
         end,
   ⟨ _, pr_dir, 
     take s, 
     le_antisymm 
       (begin 
        apply sup_le,
        {
            rw f.2.preserve_dSup,
            apply dSup_le,
            intros b hb,
            cases hb with a ha,
            cases ha with ha eqab,
            rw -eqab,
            apply le_dSup_of_le,
              exact ⟨_ , ha, rfl⟩,
            apply le_sup_left              
        },
        {
            rw g.2.preserve_dSup,
            apply dSup_le,
            intros b hb,
            cases hb with a ha,
            cases ha with ha eqab,
            rw -eqab,
            apply le_dSup_of_le,
            exact ⟨_ , ha, rfl⟩,
            apply le_sup_right
        }
        end) 
       (dSup_le (take b, 
         assume ⟨a, ha, eqa⟩,  
         begin 
         rw -eqa,
         apply h_monotone,
         apply le_dSup,
         assumption
         end
         )) 
   ⟩     

instance : has_sup (scott_continuous α β) := ⟨scott_continuous.sup⟩   
protected 
lemma le_sup_left (f g : scott_continuous α β) : f ≤ f ⊔ g := 
  take a, le_sup_left

protected 
lemma le_sup_right (f g : scott_continuous α β) : g ≤ f ⊔ g := 
  take a, le_sup_right

protected    
lemma sup_le (f g h : scott_continuous α β) : f ≤ h → g ≤ h → f ⊔ g ≤ h := 
  assume hfh hgh, take a, sup_le (hfh a) (hgh a) 

instance scott_continuous_semilattice_sup : semilattice_sup (scott_continuous α β) := 
{
    le := scott_continuous.le,
    le_refl := scott_continuous.le_refl,
    le_trans := scott_continuous.le_trans,
    le_antisymm := scott_continuous.le_antisymm,
    sup := scott_continuous.sup,
    le_sup_left := scott_continuous.le_sup_left,
    le_sup_right := scott_continuous.le_sup_right,
    sup_le := scott_continuous.sup_le
} 
-/
def sapply (f : scott_continuous α β) (s : directed α) : directed β := ⟨_, f.2.preserve_directed s⟩ 

protected
def dSup (fs : directed (scott_continuous α β)) : scott_continuous α β := 
  let s := λ a : α, {b : β | ∃ f : scott_continuous α β, f ∈ fs ∧ b = f.1 a} in   
  have s_directed : ∀ a, is_directed (s a), from 
    take a b₁ b₂, assume ⟨f₁, hf₁, eqb₁⟩  ⟨f₂, hf₂, eqb₂⟩,
      match fs.property _ _ hf₁ hf₂ with 
      | ⟨f, hf, hf₁f, hf₂f⟩ := ⟨_, ⟨_, hf, rfl⟩, 
          eq.rec_on eqb₁.symm (hf₁f _), eq.rec_on eqb₂.symm (hf₂f _)⟩ 
      end,
  let sup_fs := λ a : α, dSup ⟨_, s_directed a⟩ in 
  have sup_fs_monotone : monotone sup_fs, from 
     take a₁ a₂, assume h, dSup_le (take b, assume ⟨f, hf, eqf⟩, le_dSup_of_le ⟨_, hf, rfl⟩ (eq.rec_on eqf.symm (f.monotone h))), 
  have pr_dir : ∀ s : directed α, is_directed (set.image sup_fs s.1), 
    from take s, take b₁ b₂, assume ⟨a₁, ha₁, eqb₁⟩ ⟨a₂, ha₂, eqb₂⟩,    
       match s.property _ _ ha₁ ha₂ with 
       | ⟨a, ha, ha₁a, ha₂a⟩ := ⟨_, ⟨_, ha, rfl⟩, 
         eq.rec_on eqb₁ (sup_fs_monotone ha₁a), eq.rec_on eqb₂ (sup_fs_monotone ha₂a)⟩  
       end,
  ⟨_, pr_dir, 
   take s, 
     le_antisymm 
       (dSup_le (take b, assume ⟨f, hf, eqf⟩, 
        begin 
        rw eqf,
        rw f.2.preserve_dSup,
        apply dSup_le,
        intros b hb,
        cases hb with a ha,
        cases ha with ha eqa,
        rw -eqa,
        apply le_dSup_of_le,
        exact ⟨_, ha, rfl⟩,
        apply le_dSup,
        exact ⟨_, hf, rfl⟩  
        end
       ))
       (dSup_le (take b, assume ⟨a, ha, eqa⟩, eq.rec_on eqa (sup_fs_monotone (le_dSup ha) ) ))⟩

 
protected 
lemma le_dSup (fs : directed (scott_continuous α β))(f : scott_continuous α β) : f ∈ fs → f ≤ scott_continuous.dSup fs := 
 assume hf, take a, le_dSup ⟨_, hf, rfl⟩   

protected 
lemma dSup_le (fs : directed (scott_continuous α β)) (f : scott_continuous α β) : (∀ g ∈ fs, g ≤ f) → scott_continuous.dSup fs ≤ f := 
  assume h, take a, dSup_le (take b, assume ⟨g, hg, eqg⟩, eq.rec_on eqg.symm (h _ hg _)) 

@[simp]
lemma is_strict (f : scott_continuous α β) : f.1 ⊥ = ⊥ := f.property.is_strict

end scott_continuous

instance scott_continuous_function [directed_complete_partial_order α][directed_complete_partial_order β] : 
         has_coe (scott_continuous α β) (α → β) := ⟨ λ f, f.1 ⟩ 

instance scott_continuous_dcpo [directed_complete_partial_order α][directed_complete_partial_order β] 
 : directed_complete_partial_order (scott_continuous α β) := 
 {
     scott_continuous.scott_continuous_weak_order with
     dSup := scott_continuous.dSup,
     le_dSup := scott_continuous.le_dSup,
     dSup_le := scott_continuous.dSup_le
 }

 -- fixedpoints
section 
variables [directed_complete_partial_order α] [directed_complete_partial_order β]

lemma monotone_preserve_directed {f : α → β} : monotone f → ∀ s : directed α, is_directed (set.image f s.1) :=
begin 
intros hmono s b₁ b₂ hb₁ hb₂,  
cases hb₁ with a₁ ha₁,
cases ha₁ with ha₁ eqb₁,
cases hb₂ with a₂  ha₂,
cases ha₂ with ha₂ eqb₂,
rw [-eqb₁, -eqb₂],
cases s.property _ _ ha₁ ha₂ with a ha,
cases ha with ha h,
cases h with ha₁a ha₂a,
exact ⟨_, ⟨_, ha, rfl⟩, hmono ha₁a, hmono ha₂a⟩   
end   

def directed.map {f : α → β} : monotone f → directed α → directed β := assume hmono, take s, ⟨_, monotone_preserve_directed hmono s⟩   

lemma monotone_dSup {f : α → β} (hmono : monotone f) : ∀ {{s : directed α}}, dSup (directed.map hmono s) ≤ f (dSup s)
:= 
begin 
intro s,
apply dSup_le,
intros b hb,
cases hb with a ha,
cases ha with ha eqa,
rw -eqa,
apply hmono,
apply le_dSup,
assumption
end  

lemma ascending_chain_dSup {seq : ascending_chain α} : 
  dSup (directed.of_ascending_chain seq) ∈ seq ↔ seq.is_stationary := 
  ⟨ assume ⟨n, eqn⟩ , ⟨n, take m, assume hnm : n ≤ m, le_antisymm (seq.monotone hnm) (eq.rec_on eqn (le_dSup ⟨_, rfl⟩ ))⟩ ,
    assume ⟨n, hn ⟩ , ⟨n, le_antisymm 
                 (dSup_le (take b, assume ⟨m, hm⟩, eq.rec_on hm.symm (or.elim (le_total n m) 
                     (assume h : n ≤ m, eq.rec_on (hn _ h) (le_refl _)) 
                     (seq.monotone)))) 
                 (le_dSup ⟨_, rfl⟩) ⟩ ⟩ 
end
namespace monotone
variables [directed_complete_partial_order α] [directed_complete_partial_order β]

def ascending_chain {α} [order_bot α] {f : α → α} : monotone f → ascending_chain α := assume hmono, iter_n.to_ascending_chain hmono bot_le

def lfp {f : α → α} : monotone f → α :=  assume hmono, dSup (directed.of_ascending_chain (ascending_chain hmono))

lemma lfp_le {f : α → α} (hmono : monotone f) : hmono.lfp ≤ f hmono.lfp :=
 begin
   apply dSup_le,
   intros b hb,
   cases hb with n hn,
   rw hn,
   cases n with n,
   apply bot_le,
   apply hmono,
   apply le_dSup,
   exact ⟨_, rfl⟩  
 end

lemma le_lfp {f : α → α} (hmono : monotone f) : 
    hmono.ascending_chain.is_stationary → 
    f hmono.lfp ≤  hmono.lfp :=
 begin
  intro hst,
  rw -ascending_chain_dSup at hst,
  apply le_dSup,
  cases hst with n hn,
  assert H : hmono.lfp = iter_n f ⊥ n, apply hn,
  rw H,
  exact ⟨n+1, rfl⟩  
 end

lemma lfp_eq {f : α → α} (hmono : monotone f) : hmono.ascending_chain.is_stationary → hmono.lfp = f hmono.lfp 
:= assume hst, le_antisymm (lfp_le hmono) (le_lfp hmono hst)

end monotone

def fixed_point (f : α → α) : set α := { x | x = f x }

namespace scott_continuous
variables [directed_complete_partial_order α] 

def lfp (f : scott_continuous α α) : α := f.monotone.lfp

variable {f : scott_continuous α α}

lemma lfp_le : f.lfp ≤ f.1 f.lfp := 
    begin
    unfold lfp,
    unfold monotone.lfp,
    rw f.2.preserve_dSup,
    apply dSup_le,
    intros a ha,
    cases ha with n hn,
    rw hn,
    cases n with n, 
    apply bot_le,
    apply le_dSup,
    exact ⟨_, ⟨n, rfl⟩, rfl⟩ 
    end

lemma le_lfp : f.1 f.lfp ≤ f.lfp := 
   begin 
   unfold lfp, unfold monotone.lfp,
   rw f.2.preserve_dSup,   
   apply dSup_le_dSup,
   intros a ha,
   cases ha with a₁ ha₁,
   rw -ha₁.right,
   cases ha₁.left with n hn,
   rw hn,
   exact ⟨n+1, rfl⟩    
   end

lemma lfp_eq : f.lfp = f.1 f.lfp := le_antisymm lfp_le le_lfp 

lemma lfp_fixed_point : lfp f ∈ fixed_point f.1 := lfp_eq 

lemma lfp_least : ∀ x ∈ fixed_point f.1, lfp f ≤ x := 
  take x, assume xeq, dSup_le 
     (take a, assume ⟨n, hn⟩, eq.rec_on hn.symm 
        (nat.rec_on n bot_le (λ n iH, eq.rec_on xeq.symm (f.monotone iH)) )) 
end scott_continuous


