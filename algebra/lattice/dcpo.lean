import algebra.lattice.basic algebra.lattice.bounded_lattice 
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
end ascending_chain

def iter_n (f : α → α) (z : α) : ℕ → α 
|  0 := z 
|  (n + 1) := f $ iter_n n

namespace iter_n 
variables [weak_order α] {f : α → α}

lemma increasing_singlestep {z : α} : monotone f → z ≤ f z → ∀ {{n : ℕ}}, iter_n f z n ≤ iter_n f z (n+1) := 
  begin
    intros hmono hini n,
    induction n with n iH,
     assumption,
     apply hmono, assumption
  end     

def to_ascending_chain {f} {z} : monotone f → z ≤ f z → ascending_chain α := 
  assume hmono hini, ⟨iter_n f z, take n, begin apply increasing_singlestep, repeat {assumption} end⟩ 
end iter_n

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

end is_directed

def directed α [weak_order α] := { s : set α // is_directed s }

instance [weak_order α] : has_mem α (directed α) := ⟨ λ a s, a ∈ s.1⟩  
instance [weak_order α] : has_emptyc (directed α) := ⟨ ⟨_, is_directed.empty⟩ ⟩  
instance [weak_order α] : has_subset (directed α) := ⟨ λ s t, s.1 ⊆ t.1 ⟩ 

class directed_complete_partial_order α extends  semilattice_sup α := 
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

def top : α := dSup ⟨_, is_directed.univ⟩ 
lemma le_top : a ≤ top := le_dSup _ _ true.intro
  
end directed_complete_partial_order

instance directed_complete_partial_order_sup_bot [ ins : directed_complete_partial_order α] : semilattice_sup_bot α := 
{
  ins with 
  bot := directed_complete_partial_order.bot,
  bot_le := @directed_complete_partial_order.bot_le _ _,
}

instance directed_complete_partial_order_sup_top [ ins : directed_complete_partial_order α] : semilattice_sup_top α := 
{
  ins with 
  top := directed_complete_partial_order.top,
  le_top := @directed_complete_partial_order.le_top _ _,
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

end scott_continuous

instance scott_continuous_function [directed_complete_partial_order α][directed_complete_partial_order β] : 
         has_coe (scott_continuous α β) (α → β) := ⟨ λ f, f.1 ⟩ 

instance scott_continuous_dcpo [directed_complete_partial_order α][directed_complete_partial_order β] 
 : directed_complete_partial_order (scott_continuous α β) := 
 {
     scott_continuous.scott_continuous_semilattice_sup with
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

def monotone_ascending_chain {f : α → α} : monotone f → directed α := assume hmono,
    ⟨_, is_directed.of_ascending_chain (iter_n.to_ascending_chain hmono bot_le)⟩   
def monotone_lfp {f : α → α} : monotone f → α :=  assume hmono, dSup (monotone_ascending_chain hmono)

lemma monotone_lfp_le {f : α → α} (hmono : monotone f) : monotone_lfp hmono ≤ f (monotone_lfp hmono) :=
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

lemma monotone_le_lfp {f : α → α} (hmono : monotone f) : f (monotone_lfp hmono) ≤ monotone_lfp hmono :=  
have ∀ n, iter_n f ⊥ (n + 1) ≤ f (monotone_lfp hmono), 
   from take n, 
   begin 
   apply hmono,
   apply le_dSup,
   exact ⟨_, rfl⟩ 
   end, 
begin
      
end
def fixed_point (f : α → α) : set α := { x | x = f x }

def lfp (f : scott_continuous α α) : α := 
  dSup ⟨_, is_directed.of_ascending_chain (iter_n.to_ascending_chain f.monotone bot_le)⟩   


variable {f : scott_continuous α α}

lemma lfp_eq : lfp f = f.1 (lfp f) := 
  le_antisymm 
    begin
      unfold lfp,
      rw f.2.preserve_dSup,
      apply dSup_le,
      intros a ha,
      cases ha with n hn,
      rw hn,
      apply le_dSup_of_le,
      exact ⟨iter_n f.1 ⊥ n, ⟨_, rfl⟩ , rfl⟩,
      change iter_n f.1 ⊥ n ≤ iter_n f.1 ⊥ (n+1),
      apply iter_n.increasing_singlestep f.monotone bot_le,
    end
    begin
    unfold lfp,
    rw f.2.preserve_dSup,
    apply dSup_le,
    intros a ha,
    cases ha with a₁ ha₁,
    cases ha₁ with ha₁ eqa₁,
    cases ha₁ with n hn,
    rw -eqa₁,
    rw hn,
    apply le_dSup,
    exact ⟨n+1, rfl⟩ 
    end   

lemma lfp_fixed_point : lfp f ∈ fixed_point f.1 := lfp_eq 

lemma lfp_le : ∀ x ∈ fixed_point f.1, lfp f ≤ x := 
  take x, assume xeq, dSup_le 
     (take a, assume ⟨n, hn⟩, eq.rec_on hn.symm 
        (nat.rec_on n bot_le (λ n iH, eq.rec_on xeq.symm (f.monotone iH)) )) 
end


